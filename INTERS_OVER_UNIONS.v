Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INTERS_OVER_UNIONS_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import EXTENSION_spec.
Require Import INTERS_IMAGE_spec.
Require Import IN_UNIONS_spec.
Require Import RIGHT_IMP_EXISTS_THM_spec.
Require Import SIMPLE_IMAGE_spec.
Require Import SKOLEM_THM_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19490_spec.
Require Import thm19699_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm3184736_spec.
Require Import thm3184739_spec.
Require Import thm3458971_spec.
Require Import thm3458974_spec.
Lemma lem3477712 {A B : Type'} (P : type1413 A B) : term0 A B P.
Proof. exact (@lem13546 A B P). Qed.
Lemma lem3477713 {A B : Type'} (P : type1413 A B) : (term0 A B P) = ((term1 A B P) = (term2 A B P)).
Proof. exact (eq_refl (term0 A B P)). Qed.
Lemma lem3477715 {A : Type'} (P : Prop) : term3 A P.
Proof. exact (@lem12262 A P). Qed.
Lemma lem3477716 {A : Type'} (P : Prop) : (term3 A P) = (term4 A P).
Proof. exact (eq_refl (term3 A P)). Qed.
Lemma lem3477717 {A : Type'} (P : Prop) : term4 A P.
Proof. exact (EQ_MP (@lem3477716 A P) (@lem3477715 A P)). Qed.
Lemma lem3477718 {A : Type'} (P : Prop) (Q : A -> Prop) : term5 A P Q.
Proof. exact (@lem3477717 A P Q). Qed.
Lemma lem3477719 {A : Type'} (P : Prop) (Q : A -> Prop) : (term5 A P Q) = ((term6 A P Q) = (term7 A P Q)).
Proof. exact (eq_refl (term5 A P Q)). Qed.
Lemma lem3477745 {_83095 : Type'} : term8 _83095.
Proof. exact (EQ_MP (@lem3184739 _83095) (@lem3184736 _83095)). Qed.
Lemma lem3477746 {_83095 : Type'} (p : _83095 -> Prop) : term9 _83095 p.
Proof. exact (@lem3477745 _83095 p). Qed.
Lemma lem3477747 {_83095 : Type'} (p : _83095 -> Prop) : (term9 _83095 p) = (term10 _83095 p).
Proof. exact (eq_refl (term9 _83095 p)). Qed.
Lemma lem3477748 {_83095 : Type'} (p : _83095 -> Prop) : term10 _83095 p.
Proof. exact (EQ_MP (@lem3477747 _83095 p) (@lem3477746 _83095 p)). Qed.
Lemma lem3477749 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term11 _83095 p x.
Proof. exact (@lem3477748 _83095 p x). Qed.
Lemma lem3477750 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term11 _83095 p x) = ((term12 _83095 x p) = (p x)).
Proof. exact (eq_refl (term11 _83095 p x)). Qed.
Lemma lem3477759 {A : Type'} (s : type686 A) : term13 A s.
Proof. exact (@lem3205091 A s). Qed.
Lemma lem3477760 {A : Type'} (s : type686 A) : (term13 A s) = (term14 A s).
Proof. exact (eq_refl (term13 A s)). Qed.
Lemma lem3477761 {A : Type'} (s : type686 A) : term14 A s.
Proof. exact (EQ_MP (@lem3477760 A s) (@lem3477759 A s)). Qed.
Lemma lem3477762 {A : Type'} (s : type686 A) (x : A) : term15 A s x.
Proof. exact (@lem3477761 A s x). Qed.
Lemma lem3477763 {A : Type'} (s : type686 A) (x : A) : (term15 A s x) = ((term16 A x s) = (term17 A s x)).
Proof. exact (eq_refl (term15 A s x)). Qed.
Lemma lem3477780 {_89520 _89534 : Type'} : term18 _89520 _89534.
Proof. exact (EQ_MP (@lem3458974 _89520 _89534) (@lem3458971 _89520 _89534)). Qed.
Lemma lem3477781 {_89520 _89534 : Type'} (P : _89534 -> Prop) : term19 _89520 _89534 P.
Proof. exact (@lem3477780 _89520 _89534 P). Qed.
Lemma lem3477782 {_89520 _89534 : Type'} (P : _89534 -> Prop) : (term19 _89520 _89534 P) = (term20 _89520 _89534 P).
Proof. exact (eq_refl (term19 _89520 _89534 P)). Qed.
Lemma lem3477783 {_89520 _89534 : Type'} (P : _89534 -> Prop) : term20 _89520 _89534 P.
Proof. exact (EQ_MP (@lem3477782 _89520 _89534 P) (@lem3477781 _89520 _89534 P)). Qed.
Lemma lem3477784 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) : term21 _89520 _89534 P f.
Proof. exact (@lem3477783 _89520 _89534 P f). Qed.
Lemma lem3477785 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) : (term21 _89520 _89534 P f) = ((term22 _89520 _89534 P f) = (term23 _89520 _89534 P f)).
Proof. exact (eq_refl (term21 _89520 _89534 P f)). Qed.
Lemma lem3477793 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) : term24 _89465 _89481 f.
Proof. exact (@lem3453847 _89465 _89481 f). Qed.
Lemma lem3477794 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) : (term24 _89465 _89481 f) = (term25 _89465 _89481 f).
Proof. exact (eq_refl (term24 _89465 _89481 f)). Qed.
Lemma lem3477795 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) : term25 _89465 _89481 f.
Proof. exact (EQ_MP (@lem3477794 _89465 _89481 f) (@lem3477793 _89465 _89481 f)). Qed.
Lemma lem3477796 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) (s : _89481 -> Prop) : term26 _89465 _89481 f s.
Proof. exact (@lem3477795 _89465 _89481 f s). Qed.
Lemma lem3477797 {_89465 _89481 : Type'} (s : _89481 -> Prop) (f : type1470 _89465 _89481) : (term26 _89465 _89481 f s) = ((term27 _89465 _89481 f s) = (term28 _89465 _89481 s f)).
Proof. exact (eq_refl (term26 _89465 _89481 f s)). Qed.
Lemma lem3477799 {_88128 _88132 : Type'} (f : _88128 -> _88132) : term29 _88128 _88132 f.
Proof. exact (@lem3393993 _88128 _88132 f). Qed.
Lemma lem3477800 {_88128 _88132 : Type'} (f : _88128 -> _88132) : (term29 _88128 _88132 f) = (term30 _88128 _88132 f).
Proof. exact (eq_refl (term29 _88128 _88132 f)). Qed.
Lemma lem3477801 {_88128 _88132 : Type'} (f : _88128 -> _88132) : term30 _88128 _88132 f.
Proof. exact (EQ_MP (@lem3477800 _88128 _88132 f) (@lem3477799 _88128 _88132 f)). Qed.
Lemma lem3477802 {_88128 _88132 : Type'} (f : _88128 -> _88132) (s : _88128 -> Prop) : term31 _88128 _88132 f s.
Proof. exact (@lem3477801 _88128 _88132 f s). Qed.
Lemma lem3477803 {_88128 _88132 : Type'} (f : _88128 -> _88132) (s : _88128 -> Prop) : (term31 _88128 _88132 f s) = ((term32 _88128 _88132 s f) = (@IMAGE _88128 _88132 f s)).
Proof. exact (eq_refl (term31 _88128 _88132 f s)). Qed.
Lemma lem3477805 {A : Type'} (s : A -> Prop) : term33 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem3477806 {A : Type'} (s : A -> Prop) : (term33 A s) = (term34 A s).
Proof. exact (eq_refl (term33 A s)). Qed.
Lemma lem3477807 {A : Type'} (s : A -> Prop) : term34 A s.
Proof. exact (EQ_MP (@lem3477806 A s) (@lem3477805 A s)). Qed.
Lemma lem3477808 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term35 A s t.
Proof. exact (@lem3477807 A s t). Qed.
Lemma lem3477809 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term35 A s t) = ((s = t) = (term36 A s t)).
Proof. exact (eq_refl (term35 A s t)). Qed.
Lemma lem3477812 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term36 A s t).
Proof. exact (EQ_MP (@lem3477809 A s t) (@lem3477808 A s t)). Qed.
Lemma lem3477813 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (s = t) = (term36 B s t).
Proof. exact (@lem3477812 B s t). Qed.
Lemma lem3477814 {A B : Type'} (f : type1374 A B) (s : A -> Prop) : ((term37 A B s f) = (term38 A B f s)) = (term39 A B f s).
Proof. exact (@lem3477813 B (term37 A B s f) (term38 A B f s)). Qed.
Lemma lem3477815 {A B : Type'} (f : type1374 A B) (s : A -> Prop) : (term39 A B f s) = ((term37 A B s f) = (term38 A B f s)).
Proof. exact (SYM (@lem3477814 A B f s)). Qed.
Lemma lem3477823 {_88128 _88132 : Type'} (f : _88128 -> _88132) (s : _88128 -> Prop) : (term32 _88128 _88132 s f) = (@IMAGE _88128 _88132 f s).
Proof. exact (EQ_MP (@lem3477803 _88128 _88132 f s) (@lem3477802 _88128 _88132 f s)). Qed.
Lemma lem3477824 {A B : Type'} (f : type1413 A B) (s : A -> Prop) : (term40 A B s f) = (@IMAGE A (B -> Prop) f s).
Proof. exact (@lem3477823 A (B -> Prop) f s). Qed.
Lemma lem3477825 {A B : Type'} (f : type1374 A B) (s : A -> Prop) : (term41 A B s f) = (term42 A B f s).
Proof. exact (@lem3477824 A B (term43 A B f) s). Qed.
Lemma lem3477826 {A B : Type'} (f : type1374 A B) (x : A) : (term44 A B f x) = (term45 A B f x).
Proof. exact (eq_refl (term44 A B f x)). Qed.
Lemma lem3477827 {A B : Type'} (GEN_PVAR_70 : B -> Prop) (x : A) (s : A -> Prop) : (term46 A B GEN_PVAR_70 x s) = (term46 A B GEN_PVAR_70 x s).
Proof. exact (eq_refl (term46 A B GEN_PVAR_70 x s)). Qed.
Lemma lem3477828 {A B : Type'} (GEN_PVAR_70 : B -> Prop) (s : A -> Prop) (f : type1374 A B) (x : A) : (term47 A B GEN_PVAR_70 s f x) = (term48 A B GEN_PVAR_70 s f x).
Proof. exact (MK_COMB (@lem3477827 A B GEN_PVAR_70 x s) (@lem3477826 A B f x)). Qed.
Lemma lem3477829 {A B : Type'} (GEN_PVAR_70 : B -> Prop) (s : A -> Prop) (f : type1374 A B) : (term49 A B GEN_PVAR_70 s f) = (term50 A B GEN_PVAR_70 s f).
Proof. exact (fun_ext (fun x : A => @lem3477828 A B GEN_PVAR_70 s f x)). Qed.
Lemma lem3477830 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3477831 {A B : Type'} (GEN_PVAR_70 : B -> Prop) (s : A -> Prop) (f : type1374 A B) : (term51 A B GEN_PVAR_70 s f) = (term52 A B GEN_PVAR_70 s f).
Proof. exact (MK_COMB (@lem3477830 A) (@lem3477829 A B GEN_PVAR_70 s f)). Qed.
Lemma lem3477832 {A B : Type'} (s : A -> Prop) (f : type1374 A B) : (term53 A B s f) = (term54 A B s f).
Proof. exact (fun_ext (fun GEN_PVAR_70 : B -> Prop => @lem3477831 A B GEN_PVAR_70 s f)). Qed.
Lemma lem3477833 {B : Type'} : (@GSPEC (B -> Prop)) = (@GSPEC (B -> Prop)).
Proof. exact (eq_refl (@GSPEC (B -> Prop))). Qed.
Lemma lem3477834 {A B : Type'} (s : A -> Prop) (f : type1374 A B) : (term41 A B s f) = (term55 A B s f).
Proof. exact (MK_COMB (@lem3477833 B) (@lem3477832 A B s f)). Qed.
Lemma lem3477835 {B : Type'} : (@eq ((B -> Prop) -> Prop)) = (@eq ((B -> Prop) -> Prop)).
Proof. exact (eq_refl (@eq ((B -> Prop) -> Prop))). Qed.
Lemma lem3477836 {A B : Type'} (s : A -> Prop) (f : type1374 A B) : (term56 A B s f) = (term57 A B s f).
Proof. exact (MK_COMB (@lem3477835 B) (@lem3477834 A B s f)). Qed.
Lemma lem3477837 {A B : Type'} (f : type1374 A B) (s : A -> Prop) : (term42 A B f s) = (term42 A B f s).
Proof. exact (eq_refl (term42 A B f s)). Qed.
Lemma lem3477838 {A B : Type'} (f : type1374 A B) (s : A -> Prop) : ((term41 A B s f) = (term42 A B f s)) = ((term55 A B s f) = (term42 A B f s)).
Proof. exact (MK_COMB (@lem3477836 A B s f) (@lem3477837 A B f s)). Qed.
Lemma lem3477839 {A B : Type'} (f : type1374 A B) (s : A -> Prop) : (term55 A B s f) = (term42 A B f s).
Proof. exact (EQ_MP (@lem3477838 A B f s) (@lem3477825 A B f s)). Qed.
Lemma lem3477840 {B : Type'} : (@INTERS B) = (@INTERS B).
Proof. exact (eq_refl (@INTERS B)). Qed.
Lemma lem3477841 {A B : Type'} (f : type1374 A B) (s : A -> Prop) : (term37 A B s f) = (term58 A B f s).
Proof. exact (MK_COMB (@lem3477840 B) (@lem3477839 A B f s)). Qed.
Lemma lem3477843 {_89465 _89481 : Type'} (s : _89481 -> Prop) (f : type1470 _89465 _89481) : (term27 _89465 _89481 f s) = (term28 _89465 _89481 s f).
Proof. exact (EQ_MP (@lem3477797 _89465 _89481 s f) (@lem3477796 _89465 _89481 f s)). Qed.
Lemma lem3477844 {A B : Type'} (s : A -> Prop) (f : type1413 A B) : (term59 A B f s) = (term60 A B s f).
Proof. exact (@lem3477843 B A s f). Qed.
Lemma lem3477845 {A B : Type'} (s : A -> Prop) (f : type1374 A B) : (term58 A B f s) = (term61 A B s f).
Proof. exact (@lem3477844 A B s (term43 A B f)). Qed.
Lemma lem3477857 {A B : Type'} (f : A -> B) (y : A) : (term62 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem3477858 {A B : Type'} (f : type1413 A B) (y : A) : (term63 A B f y) = (f y).
Proof. exact (@lem3477857 A (B -> Prop) f y). Qed.
Lemma lem3477859 {A B : Type'} (f : type1374 A B) (x : A) : (term64 A B f x) = (term44 A B f x).
Proof. exact (@lem3477858 A B (term43 A B f) x). Qed.
Lemma lem3477860 {A B : Type'} (f : type1374 A B) (x : A) : (term44 A B f x) = (term45 A B f x).
Proof. exact (eq_refl (term44 A B f x)). Qed.
Lemma lem3477861 {A B : Type'} (f : type1374 A B) : (term65 A B f) = (term43 A B f).
Proof. exact (fun_ext (fun x : A => @lem3477860 A B f x)). Qed.
Lemma lem3477862 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3477863 {A B : Type'} (f : type1374 A B) (x : A) : (term64 A B f x) = (term44 A B f x).
Proof. exact (MK_COMB (@lem3477861 A B f) (@lem3477862 A x)). Qed.
Lemma lem3477864 {B : Type'} : (@eq (B -> Prop)) = (@eq (B -> Prop)).
Proof. exact (eq_refl (@eq (B -> Prop))). Qed.
Lemma lem3477865 {A B : Type'} (f : type1374 A B) (x : A) : (term66 A B f x) = (term67 A B f x).
Proof. exact (MK_COMB (@lem3477864 B) (@lem3477863 A B f x)). Qed.
Lemma lem3477866 {A B : Type'} (f : type1374 A B) (x : A) : (term44 A B f x) = (term45 A B f x).
Proof. exact (eq_refl (term44 A B f x)). Qed.
Lemma lem3477867 {A B : Type'} (f : type1374 A B) (x : A) : ((term64 A B f x) = (term44 A B f x)) = ((term44 A B f x) = (term45 A B f x)).
Proof. exact (MK_COMB (@lem3477865 A B f x) (@lem3477866 A B f x)). Qed.
Lemma lem3477868 {A B : Type'} (f : type1374 A B) (x : A) : (term44 A B f x) = (term45 A B f x).
Proof. exact (EQ_MP (@lem3477867 A B f x) (@lem3477859 A B f x)). Qed.
Lemma lem3477869 {B : Type'} (y : B) : (@IN B y) = (@IN B y).
Proof. exact (eq_refl (@IN B y)). Qed.
Lemma lem3477870 {A B : Type'} (y : B) (f : type1374 A B) (x : A) : (term68 A B y f x) = (term69 A B y f x).
Proof. exact (MK_COMB (@lem3477869 B y) (@lem3477868 A B f x)). Qed.
Lemma lem3477871 {A : Type'} (x : A) (s : A -> Prop) : (term70 A x s) = (term70 A x s).
Proof. exact (eq_refl (term70 A x s)). Qed.
Lemma lem3477872 {A B : Type'} (s : A -> Prop) (y : B) (f : type1374 A B) (x : A) : (term71 A B s y f x) = (term72 A B s y f x).
Proof. exact (MK_COMB (@lem3477871 A x s) (@lem3477870 A B y f x)). Qed.
Lemma lem3477875 {A B : Type'} (s : A -> Prop) (y : B) (f : type1374 A B) : (term73 A B s y f) = (term74 A B s y f).
Proof. exact (fun_ext (fun x : A => @lem3477872 A B s y f x)). Qed.
Lemma lem3477876 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3477877 {A B : Type'} (s : A -> Prop) (y : B) (f : type1374 A B) : (term75 A B s y f) = (term76 A B s y f).
Proof. exact (MK_COMB (@lem3477876 A) (@lem3477875 A B s y f)). Qed.
Lemma lem3477882 {B : Type'} (GEN_PVAR_48 : B) : (@SETSPEC B GEN_PVAR_48) = (@SETSPEC B GEN_PVAR_48).
Proof. exact (eq_refl (@SETSPEC B GEN_PVAR_48)). Qed.
Lemma lem3477883 {A B : Type'} (GEN_PVAR_48 : B) (s : A -> Prop) (y : B) (f : type1374 A B) : (term77 A B GEN_PVAR_48 s y f) = (term78 A B GEN_PVAR_48 s y f).
Proof. exact (MK_COMB (@lem3477882 B GEN_PVAR_48) (@lem3477877 A B s y f)). Qed.
Lemma lem3477884 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem3477885 {A B : Type'} (GEN_PVAR_48 : B) (s : A -> Prop) (f : type1374 A B) (y : B) : (term79 A B GEN_PVAR_48 s f y) = (term80 A B GEN_PVAR_48 s f y).
Proof. exact (MK_COMB (@lem3477883 A B GEN_PVAR_48 s y f) (@lem3477884 B y)). Qed.
Lemma lem3477886 {A B : Type'} (GEN_PVAR_48 : B) (s : A -> Prop) (f : type1374 A B) : (term81 A B GEN_PVAR_48 s f) = (term82 A B GEN_PVAR_48 s f).
Proof. exact (fun_ext (fun y : B => @lem3477885 A B GEN_PVAR_48 s f y)). Qed.
Lemma lem3477887 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3477888 {A B : Type'} (GEN_PVAR_48 : B) (s : A -> Prop) (f : type1374 A B) : (term83 A B GEN_PVAR_48 s f) = (term84 A B GEN_PVAR_48 s f).
Proof. exact (MK_COMB (@lem3477887 B) (@lem3477886 A B GEN_PVAR_48 s f)). Qed.
Lemma lem3477893 {A B : Type'} (s : A -> Prop) (f : type1374 A B) : (term85 A B s f) = (term86 A B s f).
Proof. exact (fun_ext (fun GEN_PVAR_48 : B => @lem3477888 A B GEN_PVAR_48 s f)). Qed.
Lemma lem3477894 {B : Type'} : (@GSPEC B) = (@GSPEC B).
Proof. exact (eq_refl (@GSPEC B)). Qed.
Lemma lem3477895 {A B : Type'} (s : A -> Prop) (f : type1374 A B) : (term61 A B s f) = (term87 A B s f).
Proof. exact (MK_COMB (@lem3477894 B) (@lem3477893 A B s f)). Qed.
Lemma lem3477896 {A B : Type'} (s : A -> Prop) (f : type1374 A B) : (term58 A B f s) = (term87 A B s f).
Proof. exact (TRANS (@lem3477845 A B s f) (@lem3477895 A B s f)). Qed.
Lemma lem3477897 {A B : Type'} (s : A -> Prop) (f : type1374 A B) : (term37 A B s f) = (term87 A B s f).
Proof. exact (TRANS (@lem3477841 A B f s) (@lem3477896 A B s f)). Qed.
Lemma lem3477898 {B : Type'} (x : B) : (@IN B x) = (@IN B x).
Proof. exact (eq_refl (@IN B x)). Qed.
Lemma lem3477899 {A B : Type'} (x : B) (s : A -> Prop) (f : type1374 A B) : (term88 A B x s f) = (term89 A B x s f).
Proof. exact (MK_COMB (@lem3477898 B x) (@lem3477897 A B s f)). Qed.
Lemma lem3477900 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3477901 {A B : Type'} (x : B) (s : A -> Prop) (f : type1374 A B) : (term90 A B x s f) = (term91 A B x s f).
Proof. exact (MK_COMB (@lem3477900) (@lem3477899 A B x s f)). Qed.
Lemma lem3477903 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) : (term22 _89520 _89534 P f) = (term23 _89520 _89534 P f).
Proof. exact (EQ_MP (@lem3477785 _89520 _89534 P f) (@lem3477784 _89520 _89534 P f)). Qed.
Lemma lem3477904 {A B : Type'} (P : type475 A B) (f : type469 A B) : (term92 A B P f) = (term93 A B P f).
Proof. exact (@lem3477903 B (type1413 A B) P f). Qed.
Lemma lem3477905 {A B : Type'} (f : type1374 A B) (s : A -> Prop) : (term94 A B f s) = (term95 A B f s).
Proof. exact (@lem3477904 A B (term96 A B s f) (term97 A B s)). Qed.
Lemma lem3477906 {A B : Type'} (s : A -> Prop) (g : type1413 A B) (f : type1374 A B) : (term98 A B s f g) = (term99 A B s g f).
Proof. exact (eq_refl (term98 A B s f g)). Qed.
Lemma lem3477907 {B : Type'} (GEN_PVAR_74 : B -> Prop) : (@SETSPEC (B -> Prop) GEN_PVAR_74) = (@SETSPEC (B -> Prop) GEN_PVAR_74).
Proof. exact (eq_refl (@SETSPEC (B -> Prop) GEN_PVAR_74)). Qed.
Lemma lem3477908 {A B : Type'} (GEN_PVAR_74 : B -> Prop) (s : A -> Prop) (g : type1413 A B) (f : type1374 A B) : (term100 A B GEN_PVAR_74 s f g) = (term101 A B GEN_PVAR_74 s g f).
Proof. exact (MK_COMB (@lem3477907 B GEN_PVAR_74) (@lem3477906 A B s g f)). Qed.
Lemma lem3477909 {A B : Type'} (s : A -> Prop) (g : type1413 A B) : (term102 A B s g) = (term103 A B s g).
Proof. exact (eq_refl (term102 A B s g)). Qed.
Lemma lem3477910 {A B : Type'} (GEN_PVAR_74 : B -> Prop) (f : type1374 A B) (s : A -> Prop) (g : type1413 A B) : (term104 A B GEN_PVAR_74 f s g) = (term105 A B GEN_PVAR_74 f s g).
Proof. exact (MK_COMB (@lem3477908 A B GEN_PVAR_74 s g f) (@lem3477909 A B s g)). Qed.
Lemma lem3477911 {A B : Type'} (GEN_PVAR_74 : B -> Prop) (f : type1374 A B) (s : A -> Prop) : (term106 A B GEN_PVAR_74 f s) = (term107 A B GEN_PVAR_74 f s).
Proof. exact (fun_ext (fun g : type1413 A B => @lem3477910 A B GEN_PVAR_74 f s g)). Qed.
Lemma lem3477912 {A B : Type'} : (@ex (A -> B -> Prop)) = (@ex (A -> B -> Prop)).
Proof. exact (eq_refl (@ex (A -> B -> Prop))). Qed.
Lemma lem3477913 {A B : Type'} (GEN_PVAR_74 : B -> Prop) (f : type1374 A B) (s : A -> Prop) : (term108 A B GEN_PVAR_74 f s) = (term109 A B GEN_PVAR_74 f s).
Proof. exact (MK_COMB (@lem3477912 A B) (@lem3477911 A B GEN_PVAR_74 f s)). Qed.
Lemma lem3477914 {A B : Type'} (f : type1374 A B) (s : A -> Prop) : (term110 A B f s) = (term111 A B f s).
Proof. exact (fun_ext (fun GEN_PVAR_74 : B -> Prop => @lem3477913 A B GEN_PVAR_74 f s)). Qed.
Lemma lem3477915 {B : Type'} : (@GSPEC (B -> Prop)) = (@GSPEC (B -> Prop)).
Proof. exact (eq_refl (@GSPEC (B -> Prop))). Qed.
Lemma lem3477916 {A B : Type'} (f : type1374 A B) (s : A -> Prop) : (term112 A B f s) = (term113 A B f s).
Proof. exact (MK_COMB (@lem3477915 B) (@lem3477914 A B f s)). Qed.
Lemma lem3477917 {B : Type'} : (@UNIONS B) = (@UNIONS B).
Proof. exact (eq_refl (@UNIONS B)). Qed.
Lemma lem3477918 {A B : Type'} (f : type1374 A B) (s : A -> Prop) : (term94 A B f s) = (term38 A B f s).
Proof. exact (MK_COMB (@lem3477917 B) (@lem3477916 A B f s)). Qed.
Lemma lem3477919 {B : Type'} : (@eq (B -> Prop)) = (@eq (B -> Prop)).
Proof. exact (eq_refl (@eq (B -> Prop))). Qed.
Lemma lem3477920 {A B : Type'} (f : type1374 A B) (s : A -> Prop) : (term114 A B f s) = (term115 A B f s).
Proof. exact (MK_COMB (@lem3477919 B) (@lem3477918 A B f s)). Qed.
Lemma lem3477921 {A B : Type'} (s : A -> Prop) (g : type1413 A B) (f : type1374 A B) : (term98 A B s f g) = (term99 A B s g f).
Proof. exact (eq_refl (term98 A B s f g)). Qed.
Lemma lem3477922 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3477923 {A B : Type'} (s : A -> Prop) (g : type1413 A B) (f : type1374 A B) : (term116 A B s f g) = (term117 A B s g f).
Proof. exact (MK_COMB (@lem3477922) (@lem3477921 A B s g f)). Qed.
Lemma lem3477924 {A B : Type'} (s : A -> Prop) (g : type1413 A B) : (term102 A B s g) = (term103 A B s g).
Proof. exact (eq_refl (term102 A B s g)). Qed.
Lemma lem3477925 {B : Type'} (a : B) : (@IN B a) = (@IN B a).
Proof. exact (eq_refl (@IN B a)). Qed.
Lemma lem3477926 {A B : Type'} (a : B) (s : A -> Prop) (g : type1413 A B) : (term118 A B a s g) = (term119 A B a s g).
Proof. exact (MK_COMB (@lem3477925 B a) (@lem3477924 A B s g)). Qed.
Lemma lem3477927 {A B : Type'} (f : type1374 A B) (a : B) (s : A -> Prop) (g : type1413 A B) : (term120 A B f a s g) = (term121 A B f a s g).
Proof. exact (MK_COMB (@lem3477923 A B s g f) (@lem3477926 A B a s g)). Qed.
Lemma lem3477928 {A B : Type'} (f : type1374 A B) (a : B) (s : A -> Prop) : (term122 A B f a s) = (term123 A B f a s).
Proof. exact (fun_ext (fun g : type1413 A B => @lem3477927 A B f a s g)). Qed.
Lemma lem3477929 {A B : Type'} : (@ex (A -> B -> Prop)) = (@ex (A -> B -> Prop)).
Proof. exact (eq_refl (@ex (A -> B -> Prop))). Qed.
Lemma lem3477930 {A B : Type'} (f : type1374 A B) (a : B) (s : A -> Prop) : (term124 A B f a s) = (term125 A B f a s).
Proof. exact (MK_COMB (@lem3477929 A B) (@lem3477928 A B f a s)). Qed.
Lemma lem3477931 {B : Type'} (GEN_PVAR_50 : B) : (@SETSPEC B GEN_PVAR_50) = (@SETSPEC B GEN_PVAR_50).
Proof. exact (eq_refl (@SETSPEC B GEN_PVAR_50)). Qed.
Lemma lem3477932 {A B : Type'} (GEN_PVAR_50 : B) (f : type1374 A B) (a : B) (s : A -> Prop) : (term126 A B GEN_PVAR_50 f a s) = (term127 A B GEN_PVAR_50 f a s).
Proof. exact (MK_COMB (@lem3477931 B GEN_PVAR_50) (@lem3477930 A B f a s)). Qed.
Lemma lem3477933 {B : Type'} (a : B) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem3477934 {A B : Type'} (GEN_PVAR_50 : B) (f : type1374 A B) (s : A -> Prop) (a : B) : (term128 A B GEN_PVAR_50 f s a) = (term129 A B GEN_PVAR_50 f s a).
Proof. exact (MK_COMB (@lem3477932 A B GEN_PVAR_50 f a s) (@lem3477933 B a)). Qed.
Lemma lem3477935 {A B : Type'} (GEN_PVAR_50 : B) (f : type1374 A B) (s : A -> Prop) : (term130 A B GEN_PVAR_50 f s) = (term131 A B GEN_PVAR_50 f s).
Proof. exact (fun_ext (fun a : B => @lem3477934 A B GEN_PVAR_50 f s a)). Qed.
Lemma lem3477936 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3477937 {A B : Type'} (GEN_PVAR_50 : B) (f : type1374 A B) (s : A -> Prop) : (term132 A B GEN_PVAR_50 f s) = (term133 A B GEN_PVAR_50 f s).
Proof. exact (MK_COMB (@lem3477936 B) (@lem3477935 A B GEN_PVAR_50 f s)). Qed.
Lemma lem3477938 {A B : Type'} (f : type1374 A B) (s : A -> Prop) : (term134 A B f s) = (term135 A B f s).
Proof. exact (fun_ext (fun GEN_PVAR_50 : B => @lem3477937 A B GEN_PVAR_50 f s)). Qed.
Lemma lem3477939 {B : Type'} : (@GSPEC B) = (@GSPEC B).
Proof. exact (eq_refl (@GSPEC B)). Qed.
Lemma lem3477940 {A B : Type'} (f : type1374 A B) (s : A -> Prop) : (term95 A B f s) = (term136 A B f s).
Proof. exact (MK_COMB (@lem3477939 B) (@lem3477938 A B f s)). Qed.
Lemma lem3477941 {A B : Type'} (f : type1374 A B) (s : A -> Prop) : ((term94 A B f s) = (term95 A B f s)) = ((term38 A B f s) = (term136 A B f s)).
Proof. exact (MK_COMB (@lem3477920 A B f s) (@lem3477940 A B f s)). Qed.
Lemma lem3477942 {A B : Type'} (f : type1374 A B) (s : A -> Prop) : (term38 A B f s) = (term136 A B f s).
Proof. exact (EQ_MP (@lem3477941 A B f s) (@lem3477905 A B f s)). Qed.
Lemma lem3477960 {_88128 _88132 : Type'} (f : _88128 -> _88132) (s : _88128 -> Prop) : (term32 _88128 _88132 s f) = (@IMAGE _88128 _88132 f s).
Proof. exact (EQ_MP (@lem3477803 _88128 _88132 f s) (@lem3477802 _88128 _88132 f s)). Qed.
Lemma lem3477961 {A B : Type'} (f : type1413 A B) (s : A -> Prop) : (term40 A B s f) = (@IMAGE A (B -> Prop) f s).
Proof. exact (@lem3477960 A (B -> Prop) f s). Qed.
Lemma lem3477962 {A B : Type'} (g : type1413 A B) (s : A -> Prop) : (term40 A B s g) = (@IMAGE A (B -> Prop) g s).
Proof. exact (@lem3477961 A B g s). Qed.
Lemma lem3477963 {B : Type'} : (@INTERS B) = (@INTERS B).
Proof. exact (eq_refl (@INTERS B)). Qed.
Lemma lem3477964 {A B : Type'} (g : type1413 A B) (s : A -> Prop) : (term103 A B s g) = (term59 A B g s).
Proof. exact (MK_COMB (@lem3477963 B) (@lem3477962 A B g s)). Qed.
Lemma lem3477966 {_89465 _89481 : Type'} (s : _89481 -> Prop) (f : type1470 _89465 _89481) : (term27 _89465 _89481 f s) = (term28 _89465 _89481 s f).
Proof. exact (EQ_MP (@lem3477797 _89465 _89481 s f) (@lem3477796 _89465 _89481 f s)). Qed.
Lemma lem3477967 {A B : Type'} (s : A -> Prop) (f : type1413 A B) : (term59 A B f s) = (term60 A B s f).
Proof. exact (@lem3477966 B A s f). Qed.
Lemma lem3477968 {A B : Type'} (s : A -> Prop) (g : type1413 A B) : (term59 A B g s) = (term60 A B s g).
Proof. exact (@lem3477967 A B s g). Qed.
Lemma lem3477979 {A B : Type'} (s : A -> Prop) (g : type1413 A B) : (term103 A B s g) = (term60 A B s g).
Proof. exact (TRANS (@lem3477964 A B g s) (@lem3477968 A B s g)). Qed.
Lemma lem3477980 {B : Type'} (a : B) : (@IN B a) = (@IN B a).
Proof. exact (eq_refl (@IN B a)). Qed.
Lemma lem3477981 {A B : Type'} (a : B) (s : A -> Prop) (g : type1413 A B) : (term119 A B a s g) = (term137 A B a s g).
Proof. exact (MK_COMB (@lem3477980 B a) (@lem3477979 A B s g)). Qed.
Lemma lem3477982 {A B : Type'} (s : A -> Prop) (g : type1413 A B) (f : type1374 A B) : (term117 A B s g f) = (term117 A B s g f).
Proof. exact (eq_refl (term117 A B s g f)). Qed.
Lemma lem3477983 {A B : Type'} (f : type1374 A B) (a : B) (s : A -> Prop) (g : type1413 A B) : (term121 A B f a s g) = (term138 A B f a s g).
Proof. exact (MK_COMB (@lem3477982 A B s g f) (@lem3477981 A B a s g)). Qed.
Lemma lem3477986 {A B : Type'} (f : type1374 A B) (a : B) (s : A -> Prop) : (term123 A B f a s) = (term139 A B f a s).
Proof. exact (fun_ext (fun g : type1413 A B => @lem3477983 A B f a s g)). Qed.
Lemma lem3477987 {A B : Type'} : (@ex (A -> B -> Prop)) = (@ex (A -> B -> Prop)).
Proof. exact (eq_refl (@ex (A -> B -> Prop))). Qed.
Lemma lem3477988 {A B : Type'} (f : type1374 A B) (a : B) (s : A -> Prop) : (term125 A B f a s) = (term140 A B f a s).
Proof. exact (MK_COMB (@lem3477987 A B) (@lem3477986 A B f a s)). Qed.
Lemma lem3477993 {B : Type'} (GEN_PVAR_50 : B) : (@SETSPEC B GEN_PVAR_50) = (@SETSPEC B GEN_PVAR_50).
Proof. exact (eq_refl (@SETSPEC B GEN_PVAR_50)). Qed.
Lemma lem3477994 {A B : Type'} (GEN_PVAR_50 : B) (f : type1374 A B) (a : B) (s : A -> Prop) : (term127 A B GEN_PVAR_50 f a s) = (term141 A B GEN_PVAR_50 f a s).
Proof. exact (MK_COMB (@lem3477993 B GEN_PVAR_50) (@lem3477988 A B f a s)). Qed.
Lemma lem3477995 {B : Type'} (a : B) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem3477996 {A B : Type'} (GEN_PVAR_50 : B) (f : type1374 A B) (s : A -> Prop) (a : B) : (term129 A B GEN_PVAR_50 f s a) = (term142 A B GEN_PVAR_50 f s a).
Proof. exact (MK_COMB (@lem3477994 A B GEN_PVAR_50 f a s) (@lem3477995 B a)). Qed.
Lemma lem3477997 {A B : Type'} (GEN_PVAR_50 : B) (f : type1374 A B) (s : A -> Prop) : (term131 A B GEN_PVAR_50 f s) = (term143 A B GEN_PVAR_50 f s).
Proof. exact (fun_ext (fun a : B => @lem3477996 A B GEN_PVAR_50 f s a)). Qed.
Lemma lem3477998 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3477999 {A B : Type'} (GEN_PVAR_50 : B) (f : type1374 A B) (s : A -> Prop) : (term133 A B GEN_PVAR_50 f s) = (term144 A B GEN_PVAR_50 f s).
Proof. exact (MK_COMB (@lem3477998 B) (@lem3477997 A B GEN_PVAR_50 f s)). Qed.
Lemma lem3478004 {A B : Type'} (f : type1374 A B) (s : A -> Prop) : (term135 A B f s) = (term145 A B f s).
Proof. exact (fun_ext (fun GEN_PVAR_50 : B => @lem3477999 A B GEN_PVAR_50 f s)). Qed.
Lemma lem3478005 {B : Type'} : (@GSPEC B) = (@GSPEC B).
Proof. exact (eq_refl (@GSPEC B)). Qed.
Lemma lem3478006 {A B : Type'} (f : type1374 A B) (s : A -> Prop) : (term136 A B f s) = (term146 A B f s).
Proof. exact (MK_COMB (@lem3478005 B) (@lem3478004 A B f s)). Qed.
Lemma lem3478007 {A B : Type'} (f : type1374 A B) (s : A -> Prop) : (term38 A B f s) = (term146 A B f s).
Proof. exact (TRANS (@lem3477942 A B f s) (@lem3478006 A B f s)). Qed.
Lemma lem3478008 {B : Type'} (x : B) : (@IN B x) = (@IN B x).
Proof. exact (eq_refl (@IN B x)). Qed.
Lemma lem3478009 {A B : Type'} (x : B) (f : type1374 A B) (s : A -> Prop) : (term147 A B x f s) = (term148 A B x f s).
Proof. exact (MK_COMB (@lem3478008 B x) (@lem3478007 A B f s)). Qed.
Lemma lem3478010 {A B : Type'} (x : B) (f : type1374 A B) (s : A -> Prop) : ((term88 A B x s f) = (term147 A B x f s)) = ((term89 A B x s f) = (term148 A B x f s)).
Proof. exact (MK_COMB (@lem3477901 A B x s f) (@lem3478009 A B x f s)). Qed.
Lemma lem3478013 {A B : Type'} (f : type1374 A B) (s : A -> Prop) : (term149 A B f s) = (term150 A B f s).
Proof. exact (fun_ext (fun x : B => @lem3478010 A B x f s)). Qed.
Lemma lem3478014 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3478015 {A B : Type'} (f : type1374 A B) (s : A -> Prop) : (term39 A B f s) = (term151 A B f s).
Proof. exact (MK_COMB (@lem3478014 B) (@lem3478013 A B f s)). Qed.
Lemma lem3478020 {A B : Type'} (f : type1374 A B) (s : A -> Prop) : (term151 A B f s) = (term39 A B f s).
Proof. exact (SYM (@lem3478015 A B f s)). Qed.
Lemma lem3478028 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term12 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3477750 _83095 p x) (@lem3477749 _83095 p x)). Qed.
Lemma lem3478029 {B : Type'} (p : B -> Prop) (x : B) : (term12 B x p) = (p x).
Proof. exact (@lem3478028 B p x). Qed.
Lemma lem3478030 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : B) : (term152 A B x s f) = (term153 A B s f x).
Proof. exact (@lem3478029 B (term154 A B s f) x). Qed.
Lemma lem3478031 {A B : Type'} (s : A -> Prop) (y : B) (f : type1374 A B) : (term153 A B s f y) = (term76 A B s y f).
Proof. exact (eq_refl (term153 A B s f y)). Qed.
Lemma lem3478032 {B : Type'} (GEN_PVAR_48 : B) : (@SETSPEC B GEN_PVAR_48) = (@SETSPEC B GEN_PVAR_48).
Proof. exact (eq_refl (@SETSPEC B GEN_PVAR_48)). Qed.
Lemma lem3478033 {A B : Type'} (GEN_PVAR_48 : B) (s : A -> Prop) (y : B) (f : type1374 A B) : (term155 A B GEN_PVAR_48 s f y) = (term78 A B GEN_PVAR_48 s y f).
Proof. exact (MK_COMB (@lem3478032 B GEN_PVAR_48) (@lem3478031 A B s y f)). Qed.
Lemma lem3478034 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem3478035 {A B : Type'} (GEN_PVAR_48 : B) (s : A -> Prop) (f : type1374 A B) (y : B) : (term156 A B GEN_PVAR_48 s f y) = (term80 A B GEN_PVAR_48 s f y).
Proof. exact (MK_COMB (@lem3478033 A B GEN_PVAR_48 s y f) (@lem3478034 B y)). Qed.
Lemma lem3478036 {A B : Type'} (GEN_PVAR_48 : B) (s : A -> Prop) (f : type1374 A B) : (term157 A B GEN_PVAR_48 s f) = (term82 A B GEN_PVAR_48 s f).
Proof. exact (fun_ext (fun y : B => @lem3478035 A B GEN_PVAR_48 s f y)). Qed.
Lemma lem3478037 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3478038 {A B : Type'} (GEN_PVAR_48 : B) (s : A -> Prop) (f : type1374 A B) : (term158 A B GEN_PVAR_48 s f) = (term84 A B GEN_PVAR_48 s f).
Proof. exact (MK_COMB (@lem3478037 B) (@lem3478036 A B GEN_PVAR_48 s f)). Qed.
Lemma lem3478039 {A B : Type'} (s : A -> Prop) (f : type1374 A B) : (term159 A B s f) = (term86 A B s f).
Proof. exact (fun_ext (fun GEN_PVAR_48 : B => @lem3478038 A B GEN_PVAR_48 s f)). Qed.
Lemma lem3478040 {B : Type'} : (@GSPEC B) = (@GSPEC B).
Proof. exact (eq_refl (@GSPEC B)). Qed.
Lemma lem3478041 {A B : Type'} (s : A -> Prop) (f : type1374 A B) : (term160 A B s f) = (term87 A B s f).
Proof. exact (MK_COMB (@lem3478040 B) (@lem3478039 A B s f)). Qed.
Lemma lem3478042 {B : Type'} (x : B) : (@IN B x) = (@IN B x).
Proof. exact (eq_refl (@IN B x)). Qed.
Lemma lem3478043 {A B : Type'} (x : B) (s : A -> Prop) (f : type1374 A B) : (term152 A B x s f) = (term89 A B x s f).
Proof. exact (MK_COMB (@lem3478042 B x) (@lem3478041 A B s f)). Qed.
Lemma lem3478044 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3478045 {A B : Type'} (x : B) (s : A -> Prop) (f : type1374 A B) : (term161 A B x s f) = (term91 A B x s f).
Proof. exact (MK_COMB (@lem3478044) (@lem3478043 A B x s f)). Qed.
Lemma lem3478046 {A B : Type'} (s : A -> Prop) (x : B) (f : type1374 A B) : (term153 A B s f x) = (term76 A B s x f).
Proof. exact (eq_refl (term153 A B s f x)). Qed.
Lemma lem3478047 {A B : Type'} (s : A -> Prop) (x : B) (f : type1374 A B) : ((term152 A B x s f) = (term153 A B s f x)) = ((term89 A B x s f) = (term76 A B s x f)).
Proof. exact (MK_COMB (@lem3478045 A B x s f) (@lem3478046 A B s x f)). Qed.
Lemma lem3478048 {A B : Type'} (s : A -> Prop) (x : B) (f : type1374 A B) : (term89 A B x s f) = (term76 A B s x f).
Proof. exact (EQ_MP (@lem3478047 A B s x f) (@lem3478030 A B s f x)). Qed.
Lemma lem3478056 {A : Type'} (s : type686 A) (x : A) : (term16 A x s) = (term17 A s x).
Proof. exact (EQ_MP (@lem3477763 A s x) (@lem3477762 A s x)). Qed.
Lemma lem3478057 {B : Type'} (s : type686 B) (x : B) : (term16 B x s) = (term17 B s x).
Proof. exact (@lem3478056 B s x). Qed.
Lemma lem3478058 {A B : Type'} (f : type1374 A B) (x : A) (x' : B) : (term69 A B x' f x) = (term162 A B f x x').
Proof. exact (@lem3478057 B (f x) x'). Qed.
Lemma lem3478065 {A : Type'} (x : A) (s : A -> Prop) : (term70 A x s) = (term70 A x s).
Proof. exact (eq_refl (term70 A x s)). Qed.
Lemma lem3478066 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : A) (x' : B) : (term72 A B s x' f x) = (term163 A B s f x x').
Proof. exact (MK_COMB (@lem3478065 A x s) (@lem3478058 A B f x x')). Qed.
Lemma lem3478069 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : B) : (term74 A B s x f) = (term164 A B s f x).
Proof. exact (fun_ext (fun x' : A => @lem3478066 A B s f x' x)). Qed.
Lemma lem3478070 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3478071 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : B) : (term76 A B s x f) = (term165 A B s f x).
Proof. exact (MK_COMB (@lem3478070 A) (@lem3478069 A B s f x)). Qed.
Lemma lem3478076 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : B) : (term89 A B x s f) = (term165 A B s f x).
Proof. exact (TRANS (@lem3478048 A B s x f) (@lem3478071 A B s f x)). Qed.
Lemma lem3478077 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3478078 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : B) : (term91 A B x s f) = (term166 A B s f x).
Proof. exact (MK_COMB (@lem3478077) (@lem3478076 A B s f x)). Qed.
Lemma lem3478080 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term12 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3477750 _83095 p x) (@lem3477749 _83095 p x)). Qed.
Lemma lem3478081 {B : Type'} (p : B -> Prop) (x : B) : (term12 B x p) = (p x).
Proof. exact (@lem3478080 B p x). Qed.
Lemma lem3478082 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term167 A B x f s) = (term168 A B f s x).
Proof. exact (@lem3478081 B (term169 A B f s) x). Qed.
Lemma lem3478083 {A B : Type'} (f : type1374 A B) (a : B) (s : A -> Prop) : (term168 A B f s a) = (term140 A B f a s).
Proof. exact (eq_refl (term168 A B f s a)). Qed.
Lemma lem3478084 {B : Type'} (GEN_PVAR_50 : B) : (@SETSPEC B GEN_PVAR_50) = (@SETSPEC B GEN_PVAR_50).
Proof. exact (eq_refl (@SETSPEC B GEN_PVAR_50)). Qed.
Lemma lem3478085 {A B : Type'} (GEN_PVAR_50 : B) (f : type1374 A B) (a : B) (s : A -> Prop) : (term170 A B GEN_PVAR_50 f s a) = (term141 A B GEN_PVAR_50 f a s).
Proof. exact (MK_COMB (@lem3478084 B GEN_PVAR_50) (@lem3478083 A B f a s)). Qed.
Lemma lem3478086 {B : Type'} (a : B) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem3478087 {A B : Type'} (GEN_PVAR_50 : B) (f : type1374 A B) (s : A -> Prop) (a : B) : (term171 A B GEN_PVAR_50 f s a) = (term142 A B GEN_PVAR_50 f s a).
Proof. exact (MK_COMB (@lem3478085 A B GEN_PVAR_50 f a s) (@lem3478086 B a)). Qed.
Lemma lem3478088 {A B : Type'} (GEN_PVAR_50 : B) (f : type1374 A B) (s : A -> Prop) : (term172 A B GEN_PVAR_50 f s) = (term143 A B GEN_PVAR_50 f s).
Proof. exact (fun_ext (fun a : B => @lem3478087 A B GEN_PVAR_50 f s a)). Qed.
Lemma lem3478089 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3478090 {A B : Type'} (GEN_PVAR_50 : B) (f : type1374 A B) (s : A -> Prop) : (term173 A B GEN_PVAR_50 f s) = (term144 A B GEN_PVAR_50 f s).
Proof. exact (MK_COMB (@lem3478089 B) (@lem3478088 A B GEN_PVAR_50 f s)). Qed.
Lemma lem3478091 {A B : Type'} (f : type1374 A B) (s : A -> Prop) : (term174 A B f s) = (term145 A B f s).
Proof. exact (fun_ext (fun GEN_PVAR_50 : B => @lem3478090 A B GEN_PVAR_50 f s)). Qed.
Lemma lem3478092 {B : Type'} : (@GSPEC B) = (@GSPEC B).
Proof. exact (eq_refl (@GSPEC B)). Qed.
Lemma lem3478093 {A B : Type'} (f : type1374 A B) (s : A -> Prop) : (term175 A B f s) = (term146 A B f s).
Proof. exact (MK_COMB (@lem3478092 B) (@lem3478091 A B f s)). Qed.
Lemma lem3478094 {B : Type'} (x : B) : (@IN B x) = (@IN B x).
Proof. exact (eq_refl (@IN B x)). Qed.
Lemma lem3478095 {A B : Type'} (x : B) (f : type1374 A B) (s : A -> Prop) : (term167 A B x f s) = (term148 A B x f s).
Proof. exact (MK_COMB (@lem3478094 B x) (@lem3478093 A B f s)). Qed.
Lemma lem3478096 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3478097 {A B : Type'} (x : B) (f : type1374 A B) (s : A -> Prop) : (term176 A B x f s) = (term177 A B x f s).
Proof. exact (MK_COMB (@lem3478096) (@lem3478095 A B x f s)). Qed.
Lemma lem3478098 {A B : Type'} (f : type1374 A B) (x : B) (s : A -> Prop) : (term168 A B f s x) = (term140 A B f x s).
Proof. exact (eq_refl (term168 A B f s x)). Qed.
Lemma lem3478099 {A B : Type'} (f : type1374 A B) (x : B) (s : A -> Prop) : ((term167 A B x f s) = (term168 A B f s x)) = ((term148 A B x f s) = (term140 A B f x s)).
Proof. exact (MK_COMB (@lem3478097 A B x f s) (@lem3478098 A B f x s)). Qed.
Lemma lem3478100 {A B : Type'} (f : type1374 A B) (x : B) (s : A -> Prop) : (term148 A B x f s) = (term140 A B f x s).
Proof. exact (EQ_MP (@lem3478099 A B f x s) (@lem3478082 A B f s x)). Qed.
Lemma lem3478114 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term12 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3477750 _83095 p x) (@lem3477749 _83095 p x)). Qed.
Lemma lem3478115 {B : Type'} (p : B -> Prop) (x : B) : (term12 B x p) = (p x).
Proof. exact (@lem3478114 B p x). Qed.
Lemma lem3478116 {A B : Type'} (s : A -> Prop) (g : type1413 A B) (x : B) : (term178 A B x s g) = (term179 A B s g x).
Proof. exact (@lem3478115 B (term180 A B s g) x). Qed.
Lemma lem3478117 {A B : Type'} (s : A -> Prop) (y : B) (g : type1413 A B) : (term179 A B s g y) = (term181 A B s y g).
Proof. exact (eq_refl (term179 A B s g y)). Qed.
Lemma lem3478118 {B : Type'} (GEN_PVAR_48 : B) : (@SETSPEC B GEN_PVAR_48) = (@SETSPEC B GEN_PVAR_48).
Proof. exact (eq_refl (@SETSPEC B GEN_PVAR_48)). Qed.
Lemma lem3478119 {A B : Type'} (GEN_PVAR_48 : B) (s : A -> Prop) (y : B) (g : type1413 A B) : (term182 A B GEN_PVAR_48 s g y) = (term183 A B GEN_PVAR_48 s y g).
Proof. exact (MK_COMB (@lem3478118 B GEN_PVAR_48) (@lem3478117 A B s y g)). Qed.
Lemma lem3478120 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem3478121 {A B : Type'} (GEN_PVAR_48 : B) (s : A -> Prop) (g : type1413 A B) (y : B) : (term184 A B GEN_PVAR_48 s g y) = (term185 A B GEN_PVAR_48 s g y).
Proof. exact (MK_COMB (@lem3478119 A B GEN_PVAR_48 s y g) (@lem3478120 B y)). Qed.
Lemma lem3478122 {A B : Type'} (GEN_PVAR_48 : B) (s : A -> Prop) (g : type1413 A B) : (term186 A B GEN_PVAR_48 s g) = (term187 A B GEN_PVAR_48 s g).
Proof. exact (fun_ext (fun y : B => @lem3478121 A B GEN_PVAR_48 s g y)). Qed.
Lemma lem3478123 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3478124 {A B : Type'} (GEN_PVAR_48 : B) (s : A -> Prop) (g : type1413 A B) : (term188 A B GEN_PVAR_48 s g) = (term189 A B GEN_PVAR_48 s g).
Proof. exact (MK_COMB (@lem3478123 B) (@lem3478122 A B GEN_PVAR_48 s g)). Qed.
Lemma lem3478125 {A B : Type'} (s : A -> Prop) (g : type1413 A B) : (term190 A B s g) = (term191 A B s g).
Proof. exact (fun_ext (fun GEN_PVAR_48 : B => @lem3478124 A B GEN_PVAR_48 s g)). Qed.
Lemma lem3478126 {B : Type'} : (@GSPEC B) = (@GSPEC B).
Proof. exact (eq_refl (@GSPEC B)). Qed.
Lemma lem3478127 {A B : Type'} (s : A -> Prop) (g : type1413 A B) : (term192 A B s g) = (term60 A B s g).
Proof. exact (MK_COMB (@lem3478126 B) (@lem3478125 A B s g)). Qed.
Lemma lem3478128 {B : Type'} (x : B) : (@IN B x) = (@IN B x).
Proof. exact (eq_refl (@IN B x)). Qed.
Lemma lem3478129 {A B : Type'} (x : B) (s : A -> Prop) (g : type1413 A B) : (term178 A B x s g) = (term137 A B x s g).
Proof. exact (MK_COMB (@lem3478128 B x) (@lem3478127 A B s g)). Qed.
Lemma lem3478130 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3478131 {A B : Type'} (x : B) (s : A -> Prop) (g : type1413 A B) : (term193 A B x s g) = (term194 A B x s g).
Proof. exact (MK_COMB (@lem3478130) (@lem3478129 A B x s g)). Qed.
Lemma lem3478132 {A B : Type'} (s : A -> Prop) (x : B) (g : type1413 A B) : (term179 A B s g x) = (term181 A B s x g).
Proof. exact (eq_refl (term179 A B s g x)). Qed.
Lemma lem3478133 {A B : Type'} (s : A -> Prop) (x : B) (g : type1413 A B) : ((term178 A B x s g) = (term179 A B s g x)) = ((term137 A B x s g) = (term181 A B s x g)).
Proof. exact (MK_COMB (@lem3478131 A B x s g) (@lem3478132 A B s x g)). Qed.
Lemma lem3478134 {A B : Type'} (s : A -> Prop) (x : B) (g : type1413 A B) : (term137 A B x s g) = (term181 A B s x g).
Proof. exact (EQ_MP (@lem3478133 A B s x g) (@lem3478116 A B s g x)). Qed.
Lemma lem3478141 {A B : Type'} (s : A -> Prop) (g : type1413 A B) (f : type1374 A B) : (term117 A B s g f) = (term117 A B s g f).
Proof. exact (eq_refl (term117 A B s g f)). Qed.
Lemma lem3478142 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) (g : type1413 A B) : (term138 A B f x s g) = (term195 A B f s x g).
Proof. exact (MK_COMB (@lem3478141 A B s g f) (@lem3478134 A B s x g)). Qed.
Lemma lem3478145 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term139 A B f x s) = (term196 A B f s x).
Proof. exact (fun_ext (fun g : type1413 A B => @lem3478142 A B f s x g)). Qed.
Lemma lem3478146 {A B : Type'} : (@ex (A -> B -> Prop)) = (@ex (A -> B -> Prop)).
Proof. exact (eq_refl (@ex (A -> B -> Prop))). Qed.
Lemma lem3478147 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term140 A B f x s) = (term197 A B f s x).
Proof. exact (MK_COMB (@lem3478146 A B) (@lem3478145 A B f s x)). Qed.
Lemma lem3478152 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term148 A B x f s) = (term197 A B f s x).
Proof. exact (TRANS (@lem3478100 A B f x s) (@lem3478147 A B f s x)). Qed.
Lemma lem3478153 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : ((term89 A B x s f) = (term148 A B x f s)) = ((term165 A B s f x) = (term197 A B f s x)).
Proof. exact (MK_COMB (@lem3478078 A B s f x) (@lem3478152 A B f s x)). Qed.
Lemma lem3478156 {A B : Type'} (f : type1374 A B) (s : A -> Prop) : (term150 A B f s) = (term198 A B f s).
Proof. exact (fun_ext (fun x : B => @lem3478153 A B f s x)). Qed.
Lemma lem3478157 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3478158 {A B : Type'} (f : type1374 A B) (s : A -> Prop) : (term151 A B f s) = (term199 A B f s).
Proof. exact (MK_COMB (@lem3478157 B) (@lem3478156 A B f s)). Qed.
Lemma lem3478163 {A B : Type'} (f : type1374 A B) (s : A -> Prop) : (term199 A B f s) = (term151 A B f s).
Proof. exact (SYM (@lem3478158 A B f s)). Qed.
Lemma lem3478171 {A : Type'} (P : Prop) (Q : A -> Prop) : (term6 A P Q) = (term7 A P Q).
Proof. exact (EQ_MP (@lem3477719 A P Q) (@lem3477718 A P Q)). Qed.
Lemma lem3478172 {B : Type'} (P : Prop) (Q : type686 B) : (term200 B P Q) = (term201 B P Q).
Proof. exact (@lem3478171 (B -> Prop) P Q). Qed.
Lemma lem3478173 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : A) (b : B) : (term202 A B s f x b) = (term203 A B s f x b).
Proof. exact (@lem3478172 B (@IN A x s) (term204 A B f x b)). Qed.
Lemma lem3478174 {A B : Type'} (f : type1374 A B) (x : A) (b : B) (t : B -> Prop) : (term205 A B f x b t) = (term206 A B f x b t).
Proof. exact (eq_refl (term205 A B f x b t)). Qed.
Lemma lem3478175 {A B : Type'} (f : type1374 A B) (x : A) (b : B) : (term207 A B f x b) = (term204 A B f x b).
Proof. exact (fun_ext (fun t : B -> Prop => @lem3478174 A B f x b t)). Qed.
Lemma lem3478176 {B : Type'} : (@ex (B -> Prop)) = (@ex (B -> Prop)).
Proof. exact (eq_refl (@ex (B -> Prop))). Qed.
Lemma lem3478177 {A B : Type'} (f : type1374 A B) (x : A) (b : B) : (term208 A B f x b) = (term162 A B f x b).
Proof. exact (MK_COMB (@lem3478176 B) (@lem3478175 A B f x b)). Qed.
Lemma lem3478178 {A : Type'} (x : A) (s : A -> Prop) : (term70 A x s) = (term70 A x s).
Proof. exact (eq_refl (term70 A x s)). Qed.
Lemma lem3478179 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : A) (b : B) : (term202 A B s f x b) = (term163 A B s f x b).
Proof. exact (MK_COMB (@lem3478178 A x s) (@lem3478177 A B f x b)). Qed.
Lemma lem3478180 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3478181 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : A) (b : B) : (term209 A B s f x b) = (term210 A B s f x b).
Proof. exact (MK_COMB (@lem3478180) (@lem3478179 A B s f x b)). Qed.
Lemma lem3478182 {A B : Type'} (f : type1374 A B) (x : A) (b : B) (t : B -> Prop) : (term205 A B f x b t) = (term206 A B f x b t).
Proof. exact (eq_refl (term205 A B f x b t)). Qed.
Lemma lem3478183 {A : Type'} (x : A) (s : A -> Prop) : (term70 A x s) = (term70 A x s).
Proof. exact (eq_refl (term70 A x s)). Qed.
Lemma lem3478184 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : A) (b : B) (t : B -> Prop) : (term211 A B s f x b t) = (term212 A B s f x b t).
Proof. exact (MK_COMB (@lem3478183 A x s) (@lem3478182 A B f x b t)). Qed.
Lemma lem3478185 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : A) (b : B) : (term213 A B s f x b) = (term214 A B s f x b).
Proof. exact (fun_ext (fun t : B -> Prop => @lem3478184 A B s f x b t)). Qed.
Lemma lem3478186 {B : Type'} : (@ex (B -> Prop)) = (@ex (B -> Prop)).
Proof. exact (eq_refl (@ex (B -> Prop))). Qed.
Lemma lem3478187 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : A) (b : B) : (term203 A B s f x b) = (term215 A B s f x b).
Proof. exact (MK_COMB (@lem3478186 B) (@lem3478185 A B s f x b)). Qed.
Lemma lem3478188 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : A) (b : B) : ((term202 A B s f x b) = (term203 A B s f x b)) = ((term163 A B s f x b) = (term215 A B s f x b)).
Proof. exact (MK_COMB (@lem3478181 A B s f x b) (@lem3478187 A B s f x b)). Qed.
Lemma lem3478189 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : A) (b : B) : (term163 A B s f x b) = (term215 A B s f x b).
Proof. exact (EQ_MP (@lem3478188 A B s f x b) (@lem3478173 A B s f x b)). Qed.
Lemma lem3478198 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) : (term164 A B s f b) = (term216 A B s f b).
Proof. exact (fun_ext (fun x : A => @lem3478189 A B s f x b)). Qed.
Lemma lem3478199 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3478200 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) : (term165 A B s f b) = (term217 A B s f b).
Proof. exact (MK_COMB (@lem3478199 A) (@lem3478198 A B s f b)). Qed.
Lemma lem3478202 {A B : Type'} (P : type1413 A B) : (term1 A B P) = (term2 A B P).
Proof. exact (EQ_MP (@lem3477713 A B P) (@lem3477712 A B P)). Qed.
Lemma lem3478203 {A B : Type'} (P : type1374 A B) : (term218 A B P) = (term219 A B P).
Proof. exact (@lem3478202 A (B -> Prop) P). Qed.
Lemma lem3478204 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) : (term220 A B s f b) = (term221 A B s f b).
Proof. exact (@lem3478203 A B (term222 A B s f b)). Qed.
Lemma lem3478205 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : A) (b : B) : (term223 A B s f b x) = (term214 A B s f x b).
Proof. exact (eq_refl (term223 A B s f b x)). Qed.
Lemma lem3478206 {B : Type'} (t : B -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem3478207 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : A) (b : B) (t : B -> Prop) : (term224 A B s f b x t) = (term225 A B s f x b t).
Proof. exact (MK_COMB (@lem3478205 A B s f x b) (@lem3478206 B t)). Qed.
Lemma lem3478208 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : A) (b : B) (t : B -> Prop) : (term225 A B s f x b t) = (term212 A B s f x b t).
Proof. exact (eq_refl (term225 A B s f x b t)). Qed.
Lemma lem3478209 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : A) (b : B) (t : B -> Prop) : (term224 A B s f b x t) = (term212 A B s f x b t).
Proof. exact (TRANS (@lem3478207 A B s f x b t) (@lem3478208 A B s f x b t)). Qed.
Lemma lem3478210 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : A) (b : B) : (term226 A B s f b x) = (term214 A B s f x b).
Proof. exact (fun_ext (fun t : B -> Prop => @lem3478209 A B s f x b t)). Qed.
Lemma lem3478211 {B : Type'} : (@ex (B -> Prop)) = (@ex (B -> Prop)).
Proof. exact (eq_refl (@ex (B -> Prop))). Qed.
Lemma lem3478212 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : A) (b : B) : (term227 A B s f b x) = (term215 A B s f x b).
Proof. exact (MK_COMB (@lem3478211 B) (@lem3478210 A B s f x b)). Qed.
Lemma lem3478213 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) : (term228 A B s f b) = (term216 A B s f b).
Proof. exact (fun_ext (fun x : A => @lem3478212 A B s f x b)). Qed.
Lemma lem3478214 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3478215 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) : (term220 A B s f b) = (term217 A B s f b).
Proof. exact (MK_COMB (@lem3478214 A) (@lem3478213 A B s f b)). Qed.
Lemma lem3478216 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3478217 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) : (term229 A B s f b) = (term230 A B s f b).
Proof. exact (MK_COMB (@lem3478216) (@lem3478215 A B s f b)). Qed.
Lemma lem3478218 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : A) (b : B) : (term223 A B s f b x) = (term214 A B s f x b).
Proof. exact (eq_refl (term223 A B s f b x)). Qed.
Lemma lem3478219 {A B : Type'} (t : type1413 A B) (x : A) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem3478220 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) (t : type1413 A B) (x : A) : (term231 A B s f b t x) = (term232 A B s f b t x).
Proof. exact (MK_COMB (@lem3478218 A B s f x b) (@lem3478219 A B t x)). Qed.
Lemma lem3478221 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) (t : type1413 A B) (x : A) : (term232 A B s f b t x) = (term233 A B s f b t x).
Proof. exact (eq_refl (term232 A B s f b t x)). Qed.
Lemma lem3478222 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) (t : type1413 A B) (x : A) : (term231 A B s f b t x) = (term233 A B s f b t x).
Proof. exact (TRANS (@lem3478220 A B s f b t x) (@lem3478221 A B s f b t x)). Qed.
Lemma lem3478223 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) (t : type1413 A B) : (term234 A B s f b t) = (term235 A B s f b t).
Proof. exact (fun_ext (fun x : A => @lem3478222 A B s f b t x)). Qed.
Lemma lem3478224 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3478225 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) (t : type1413 A B) : (term236 A B s f b t) = (term237 A B s f b t).
Proof. exact (MK_COMB (@lem3478224 A) (@lem3478223 A B s f b t)). Qed.
Lemma lem3478226 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) : (term238 A B s f b) = (term239 A B s f b).
Proof. exact (fun_ext (fun t : type1413 A B => @lem3478225 A B s f b t)). Qed.
Lemma lem3478227 {A B : Type'} : (@ex (A -> B -> Prop)) = (@ex (A -> B -> Prop)).
Proof. exact (eq_refl (@ex (A -> B -> Prop))). Qed.
Lemma lem3478228 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) : (term221 A B s f b) = (term240 A B s f b).
Proof. exact (MK_COMB (@lem3478227 A B) (@lem3478226 A B s f b)). Qed.
Lemma lem3478229 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) : ((term220 A B s f b) = (term221 A B s f b)) = ((term217 A B s f b) = (term240 A B s f b)).
Proof. exact (MK_COMB (@lem3478217 A B s f b) (@lem3478228 A B s f b)). Qed.
Lemma lem3478230 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) : (term217 A B s f b) = (term240 A B s f b).
Proof. exact (EQ_MP (@lem3478229 A B s f b) (@lem3478204 A B s f b)). Qed.
Lemma lem3478243 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) : (term165 A B s f b) = (term240 A B s f b).
Proof. exact (TRANS (@lem3478200 A B s f b) (@lem3478230 A B s f b)). Qed.
Lemma lem3478244 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3478245 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) : (term166 A B s f b) = (term241 A B s f b).
Proof. exact (MK_COMB (@lem3478244) (@lem3478243 A B s f b)). Qed.
Lemma lem3478264 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : (term197 A B f s b) = (term197 A B f s b).
Proof. exact (eq_refl (term197 A B f s b)). Qed.
Lemma lem3478265 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : ((term165 A B s f b) = (term197 A B f s b)) = ((term240 A B s f b) = (term197 A B f s b)).
Proof. exact (MK_COMB (@lem3478245 A B s f b) (@lem3478264 A B f s b)). Qed.
Lemma lem3478268 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : ((term240 A B s f b) = (term197 A B f s b)) = ((term165 A B s f b) = (term197 A B f s b)).
Proof. exact (SYM (@lem3478265 A B f s b)). Qed.
Lemma lem3478270 (p : Prop) : p = (term242 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3478271 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : ((term240 A B s f b) = (term197 A B f s b)) = (term243 A B f s b).
Proof. exact (@lem3478270 ((term240 A B s f b) = (term197 A B f s b))). Qed.
Lemma lem3478272 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : (term243 A B f s b) = ((term240 A B s f b) = (term197 A B f s b)).
Proof. exact (SYM (@lem3478271 A B f s b)). Qed.
Lemma lem3478273 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) (h1 : term244 A B f s b) : term244 A B f s b.
Proof. exact (h1). Qed.
Lemma lem3478276 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) (h1 : term243 A B f s b) : term243 A B f s b.
Proof. exact (h1). Qed.
Lemma lem3478277 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : term245 A B f s b.
Proof. exact (fun h0 : term243 A B f s b => @lem3478276 A B f s b h0). Qed.
Lemma lem3478278 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) (h1 : term245 A B f s b) : term245 A B f s b.
Proof. exact (h1). Qed.
Lemma lem3478279 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) (h1 : term243 A B f s b) : term243 A B f s b.
Proof. exact (h1). Qed.
Lemma lem3478280 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) (h1 : term243 A B f s b) (h2 : term245 A B f s b) : term243 A B f s b.
Proof. exact (@lem3478278 A B f s b h2 (@lem3478279 A B f s b h1)). Qed.
Lemma lem3478281 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) (h1 : term243 A B f s b) : term246 A B f s b.
Proof. exact (fun h0 : term245 A B f s b => @lem3478280 A B f s b h1 h0). Qed.
Lemma lem3478282 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) (h1 : term245 A B f s b) : term245 A B f s b.
Proof. exact (h1). Qed.
Lemma lem3478283 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) (h1 : term243 A B f s b) (h2 : term245 A B f s b) : term243 A B f s b.
Proof. exact (@lem3478281 A B f s b h1 (@lem3478282 A B f s b h2)). Qed.
Lemma lem3478284 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) (h1 : term245 A B f s b) : term245 A B f s b.
Proof. exact (fun h0 : term243 A B f s b => @lem3478283 A B f s b h0 h1). Qed.
Lemma lem3478285 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : term247 A B f s b.
Proof. exact (fun h0 : term245 A B f s b => @lem3478284 A B f s b h0). Qed.
Lemma lem3478288 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : term245 A B f s b.
Proof. exact (@lem3478285 A B f s b (@lem3478277 A B f s b)). Qed.
Lemma lem3478289 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : term245 A B f s b.
Proof. exact (@lem3478288 A B f s b). Qed.
Lemma lem3478303 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3478304 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : (term243 A B f s b) = (term248 A B f s b).
Proof. exact (@lem3478303 (term244 A B f s b)). Qed.
Lemma lem3478306 (t : Prop) : (term249 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3478307 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : (term248 A B f s b) = ((term240 A B s f b) = (term197 A B f s b)).
Proof. exact (@lem3478306 ((term240 A B s f b) = (term197 A B f s b))). Qed.
Lemma lem3478308 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : (term243 A B f s b) = ((term240 A B s f b) = (term197 A B f s b)).
Proof. exact (TRANS (@lem3478304 A B f s b) (@lem3478307 A B f s b)). Qed.
Lemma lem3478383 {A B : Type'} (s : A -> Prop) (b : B) : (term250 A B s b) = (term251 A B s b).
Proof. exact (fun_ext (fun f : type1374 A B => @lem3478308 A B f s b)). Qed.
Lemma lem3478384 {A B : Type'} : (@all (A -> (B -> Prop) -> Prop)) = (@all (A -> (B -> Prop) -> Prop)).
Proof. exact (eq_refl (@all (A -> (B -> Prop) -> Prop))). Qed.
Lemma lem3478385 {A B : Type'} (s : A -> Prop) (b : B) : (term252 A B s b) = (term253 A B s b).
Proof. exact (MK_COMB (@lem3478384 A B) (@lem3478383 A B s b)). Qed.
Lemma lem3478390 {A B : Type'} (b : B) : (term254 A B b) = (term255 A B b).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3478385 A B s b)). Qed.
Lemma lem3478391 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3478392 {A B : Type'} (b : B) : (term256 A B b) = (term257 A B b).
Proof. exact (MK_COMB (@lem3478391 A) (@lem3478390 A B b)). Qed.
Lemma lem3478397 {A B : Type'} : (term258 A B) = (term259 A B).
Proof. exact (fun_ext (fun b : B => @lem3478392 A B b)). Qed.
Lemma lem3478398 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3478407 {A B : Type'} : (term260 A B) = (term261 A B).
Proof. exact (MK_COMB (@lem3478398 B) (@lem3478397 A B)). Qed.
Lemma lem3478412 {A B : Type'} (s : A -> Prop) (b : B) (g : type1413 A B) (x : A) : (term262 A B s b g x) = (term262 A B s b g x).
Proof. exact (eq_refl (term262 A B s b g x)). Qed.
Lemma lem3478413 {A B : Type'} (s : A -> Prop) (b : B) (g : type1413 A B) : (term263 A B s b g) = (term263 A B s b g).
Proof. exact (fun_ext (fun x : A => @lem3478412 A B s b g x)). Qed.
Lemma lem3478414 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3478415 {A B : Type'} (s : A -> Prop) (b : B) (g : type1413 A B) : (term181 A B s b g) = (term181 A B s b g).
Proof. exact (MK_COMB (@lem3478414 A) (@lem3478413 A B s b g)). Qed.
Lemma lem3478420 {A B : Type'} (s : A -> Prop) (g : type1413 A B) (f : type1374 A B) (x : A) : (term264 A B s g f x) = (term264 A B s g f x).
Proof. exact (eq_refl (term264 A B s g f x)). Qed.
Lemma lem3478421 {A B : Type'} (s : A -> Prop) (g : type1413 A B) (f : type1374 A B) : (term265 A B s g f) = (term265 A B s g f).
Proof. exact (fun_ext (fun x : A => @lem3478420 A B s g f x)). Qed.
Lemma lem3478422 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3478423 {A B : Type'} (s : A -> Prop) (g : type1413 A B) (f : type1374 A B) : (term99 A B s g f) = (term99 A B s g f).
Proof. exact (MK_COMB (@lem3478422 A) (@lem3478421 A B s g f)). Qed.
Lemma lem3478424 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3478425 {A B : Type'} (s : A -> Prop) (g : type1413 A B) (f : type1374 A B) : (term117 A B s g f) = (term117 A B s g f).
Proof. exact (MK_COMB (@lem3478424) (@lem3478423 A B s g f)). Qed.
Lemma lem3478426 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) (g : type1413 A B) : (term195 A B f s b g) = (term195 A B f s b g).
Proof. exact (MK_COMB (@lem3478425 A B s g f) (@lem3478415 A B s b g)). Qed.
Lemma lem3478427 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : (term196 A B f s b) = (term196 A B f s b).
Proof. exact (fun_ext (fun g : type1413 A B => @lem3478426 A B f s b g)). Qed.
Lemma lem3478428 {A B : Type'} : (@ex (A -> B -> Prop)) = (@ex (A -> B -> Prop)).
Proof. exact (eq_refl (@ex (A -> B -> Prop))). Qed.
Lemma lem3478429 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : (term197 A B f s b) = (term197 A B f s b).
Proof. exact (MK_COMB (@lem3478428 A B) (@lem3478427 A B f s b)). Qed.
Lemma lem3478438 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) (t : type1413 A B) (x : A) : (term233 A B s f b t x) = (term233 A B s f b t x).
Proof. exact (eq_refl (term233 A B s f b t x)). Qed.
Lemma lem3478439 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) (t : type1413 A B) : (term235 A B s f b t) = (term235 A B s f b t).
Proof. exact (fun_ext (fun x : A => @lem3478438 A B s f b t x)). Qed.
Lemma lem3478440 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3478441 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) (t : type1413 A B) : (term237 A B s f b t) = (term237 A B s f b t).
Proof. exact (MK_COMB (@lem3478440 A) (@lem3478439 A B s f b t)). Qed.
Lemma lem3478442 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) : (term239 A B s f b) = (term239 A B s f b).
Proof. exact (fun_ext (fun t : type1413 A B => @lem3478441 A B s f b t)). Qed.
Lemma lem3478443 {A B : Type'} : (@ex (A -> B -> Prop)) = (@ex (A -> B -> Prop)).
Proof. exact (eq_refl (@ex (A -> B -> Prop))). Qed.
Lemma lem3478444 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) : (term240 A B s f b) = (term240 A B s f b).
Proof. exact (MK_COMB (@lem3478443 A B) (@lem3478442 A B s f b)). Qed.
Lemma lem3478445 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3478446 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) : (term241 A B s f b) = (term241 A B s f b).
Proof. exact (MK_COMB (@lem3478445) (@lem3478444 A B s f b)). Qed.
Lemma lem3478447 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : ((term240 A B s f b) = (term197 A B f s b)) = ((term240 A B s f b) = (term197 A B f s b)).
Proof. exact (MK_COMB (@lem3478446 A B s f b) (@lem3478429 A B f s b)). Qed.
Lemma lem3478448 {A B : Type'} (s : A -> Prop) (b : B) : (term251 A B s b) = (term251 A B s b).
Proof. exact (fun_ext (fun f : type1374 A B => @lem3478447 A B f s b)). Qed.
Lemma lem3478449 {A B : Type'} : (@all (A -> (B -> Prop) -> Prop)) = (@all (A -> (B -> Prop) -> Prop)).
Proof. exact (eq_refl (@all (A -> (B -> Prop) -> Prop))). Qed.
Lemma lem3478450 {A B : Type'} (s : A -> Prop) (b : B) : (term253 A B s b) = (term253 A B s b).
Proof. exact (MK_COMB (@lem3478449 A B) (@lem3478448 A B s b)). Qed.
Lemma lem3478451 {A B : Type'} (b : B) : (term255 A B b) = (term255 A B b).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3478450 A B s b)). Qed.
Lemma lem3478452 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3478453 {A B : Type'} (b : B) : (term257 A B b) = (term257 A B b).
Proof. exact (MK_COMB (@lem3478452 A) (@lem3478451 A B b)). Qed.
Lemma lem3478454 {A B : Type'} : (term259 A B) = (term259 A B).
Proof. exact (fun_ext (fun b : B => @lem3478453 A B b)). Qed.
Lemma lem3478455 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3478456 {A B : Type'} : (term261 A B) = (term261 A B).
Proof. exact (MK_COMB (@lem3478455 B) (@lem3478454 A B)). Qed.
Lemma lem3478517 {A B : Type'} : (term260 A B) = (term261 A B).
Proof. exact (TRANS (@lem3478407 A B) (@lem3478456 A B)). Qed.
Lemma lem3478518 {A B : Type'} : (term261 A B) = (term260 A B).
Proof. exact (SYM (@lem3478517 A B)). Qed.
Lemma lem3478520 (p : Prop) : p = (term242 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3478521 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : ((term240 A B s f b) = (term197 A B f s b)) = (term243 A B f s b).
Proof. exact (@lem3478520 ((term240 A B s f b) = (term197 A B f s b))). Qed.
Lemma lem3478522 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : (term243 A B f s b) = ((term240 A B s f b) = (term197 A B f s b)).
Proof. exact (SYM (@lem3478521 A B f s b)). Qed.
Lemma lem3478523 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) (h1 : term244 A B f s b) : term244 A B f s b.
Proof. exact (h1). Qed.
Lemma lem3478534 {A B : Type'} (f : type1374 A B) (b : B) (t : type1413 A B) (x : A) : (term266 A B f b t x) = (term267 A B f b t x).
Proof. exact (@lem17045 (term268 A B t f x) (term269 A B b t x)). Qed.
Lemma lem3478539 {A : Type'} (x : A) (s : A -> Prop) : (term270 A x s) = (term270 A x s).
Proof. exact (eq_refl (term270 A x s)). Qed.
Lemma lem3478540 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) (t : type1413 A B) (x : A) : (term271 A B s f b t x) = (term272 A B s f b t x).
Proof. exact (MK_COMB (@lem3478539 A x s) (@lem3478534 A B f b t x)). Qed.
Lemma lem3478541 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) (t : type1413 A B) (x : A) : (term273 A B s f b t x) = (term271 A B s f b t x).
Proof. exact (@lem17362 (@IN A x s) (term274 A B f b t x)). Qed.
Lemma lem3478542 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) (t : type1413 A B) (x : A) : (term273 A B s f b t x) = (term272 A B s f b t x).
Proof. exact (TRANS (@lem3478541 A B s f b t x) (@lem3478540 A B s f b t x)). Qed.
Lemma lem3478547 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) (t : type1413 A B) (x : A) : (term233 A B s f b t x) = (term275 A B s f b t x).
Proof. exact (@lem17265 (@IN A x s) (term274 A B f b t x)). Qed.
Lemma lem3478548 {A : Type'} (P : A -> Prop) : (term276 A P) = (term277 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3478549 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) (t : type1413 A B) : (term278 A B s f b t) = (term279 A B s f b t).
Proof. exact (@lem3478548 A (term235 A B s f b t)). Qed.
Lemma lem3478550 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) (t : type1413 A B) (x : A) : (term280 A B s f b t x) = (term233 A B s f b t x).
Proof. exact (eq_refl (term280 A B s f b t x)). Qed.
Lemma lem3478551 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3478552 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) (t : type1413 A B) (x : A) : (term281 A B s f b t x) = (term273 A B s f b t x).
Proof. exact (MK_COMB (@lem3478551) (@lem3478550 A B s f b t x)). Qed.
Lemma lem3478553 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) (t : type1413 A B) (x : A) : (term281 A B s f b t x) = (term272 A B s f b t x).
Proof. exact (TRANS (@lem3478552 A B s f b t x) (@lem3478542 A B s f b t x)). Qed.
Lemma lem3478554 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) (t : type1413 A B) : (term282 A B s f b t) = (term283 A B s f b t).
Proof. exact (fun_ext (fun x : A => @lem3478553 A B s f b t x)). Qed.
Lemma lem3478555 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3478556 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) (t : type1413 A B) : (term279 A B s f b t) = (term284 A B s f b t).
Proof. exact (MK_COMB (@lem3478555 A) (@lem3478554 A B s f b t)). Qed.
Lemma lem3478557 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) (t : type1413 A B) : (term278 A B s f b t) = (term284 A B s f b t).
Proof. exact (TRANS (@lem3478549 A B s f b t) (@lem3478556 A B s f b t)). Qed.
Lemma lem3478558 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) (t : type1413 A B) : (term235 A B s f b t) = (term285 A B s f b t).
Proof. exact (fun_ext (fun x : A => @lem3478547 A B s f b t x)). Qed.
Lemma lem3478559 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3478560 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) (t : type1413 A B) : (term237 A B s f b t) = (term286 A B s f b t).
Proof. exact (MK_COMB (@lem3478559 A) (@lem3478558 A B s f b t)). Qed.
Lemma lem3478561 {A B : Type'} (P : type475 A B) : (term287 A B P) = (term288 A B P).
Proof. exact (@lem18394 (type1413 A B) P). Qed.
Lemma lem3478562 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) : (term289 A B s f b) = (term290 A B s f b).
Proof. exact (@lem3478561 A B (term239 A B s f b)). Qed.
Lemma lem3478563 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) (t : type1413 A B) : (term291 A B s f b t) = (term237 A B s f b t).
Proof. exact (eq_refl (term291 A B s f b t)). Qed.
Lemma lem3478564 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3478565 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) (t : type1413 A B) : (term292 A B s f b t) = (term278 A B s f b t).
Proof. exact (MK_COMB (@lem3478564) (@lem3478563 A B s f b t)). Qed.
Lemma lem3478566 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) (t : type1413 A B) : (term292 A B s f b t) = (term284 A B s f b t).
Proof. exact (TRANS (@lem3478565 A B s f b t) (@lem3478557 A B s f b t)). Qed.
Lemma lem3478567 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) : (term293 A B s f b) = (term294 A B s f b).
Proof. exact (fun_ext (fun t : type1413 A B => @lem3478566 A B s f b t)). Qed.
Lemma lem3478568 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem3478569 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) : (term290 A B s f b) = (term295 A B s f b).
Proof. exact (MK_COMB (@lem3478568 A B) (@lem3478567 A B s f b)). Qed.
Lemma lem3478570 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) : (term289 A B s f b) = (term295 A B s f b).
Proof. exact (TRANS (@lem3478562 A B s f b) (@lem3478569 A B s f b)). Qed.
Lemma lem3478571 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) : (term239 A B s f b) = (term296 A B s f b).
Proof. exact (fun_ext (fun t : type1413 A B => @lem3478560 A B s f b t)). Qed.
Lemma lem3478572 {A B : Type'} : (@ex (A -> B -> Prop)) = (@ex (A -> B -> Prop)).
Proof. exact (eq_refl (@ex (A -> B -> Prop))). Qed.
Lemma lem3478573 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) : (term240 A B s f b) = (term297 A B s f b).
Proof. exact (MK_COMB (@lem3478572 A B) (@lem3478571 A B s f b)). Qed.
Lemma lem3478582 {A B : Type'} (s : A -> Prop) (g : type1413 A B) (f : type1374 A B) (x : A) : (term298 A B s g f x) = (term299 A B s g f x).
Proof. exact (@lem17362 (@IN A x s) (term268 A B g f x)). Qed.
Lemma lem3478587 {A B : Type'} (s : A -> Prop) (g : type1413 A B) (f : type1374 A B) (x : A) : (term264 A B s g f x) = (term300 A B s g f x).
Proof. exact (@lem17265 (@IN A x s) (term268 A B g f x)). Qed.
Lemma lem3478588 {A : Type'} (P : A -> Prop) : (term276 A P) = (term277 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3478589 {A B : Type'} (s : A -> Prop) (g : type1413 A B) (f : type1374 A B) : (term301 A B s g f) = (term302 A B s g f).
Proof. exact (@lem3478588 A (term265 A B s g f)). Qed.
Lemma lem3478590 {A B : Type'} (s : A -> Prop) (g : type1413 A B) (f : type1374 A B) (x : A) : (term303 A B s g f x) = (term264 A B s g f x).
Proof. exact (eq_refl (term303 A B s g f x)). Qed.
Lemma lem3478591 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3478592 {A B : Type'} (s : A -> Prop) (g : type1413 A B) (f : type1374 A B) (x : A) : (term304 A B s g f x) = (term298 A B s g f x).
Proof. exact (MK_COMB (@lem3478591) (@lem3478590 A B s g f x)). Qed.
Lemma lem3478593 {A B : Type'} (s : A -> Prop) (g : type1413 A B) (f : type1374 A B) (x : A) : (term304 A B s g f x) = (term299 A B s g f x).
Proof. exact (TRANS (@lem3478592 A B s g f x) (@lem3478582 A B s g f x)). Qed.
Lemma lem3478594 {A B : Type'} (s : A -> Prop) (g : type1413 A B) (f : type1374 A B) : (term305 A B s g f) = (term306 A B s g f).
Proof. exact (fun_ext (fun x : A => @lem3478593 A B s g f x)). Qed.
Lemma lem3478595 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3478596 {A B : Type'} (s : A -> Prop) (g : type1413 A B) (f : type1374 A B) : (term302 A B s g f) = (term307 A B s g f).
Proof. exact (MK_COMB (@lem3478595 A) (@lem3478594 A B s g f)). Qed.
Lemma lem3478597 {A B : Type'} (s : A -> Prop) (g : type1413 A B) (f : type1374 A B) : (term301 A B s g f) = (term307 A B s g f).
Proof. exact (TRANS (@lem3478589 A B s g f) (@lem3478596 A B s g f)). Qed.
Lemma lem3478598 {A B : Type'} (s : A -> Prop) (g : type1413 A B) (f : type1374 A B) : (term265 A B s g f) = (term308 A B s g f).
Proof. exact (fun_ext (fun x : A => @lem3478587 A B s g f x)). Qed.
Lemma lem3478599 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3478600 {A B : Type'} (s : A -> Prop) (g : type1413 A B) (f : type1374 A B) : (term99 A B s g f) = (term309 A B s g f).
Proof. exact (MK_COMB (@lem3478599 A) (@lem3478598 A B s g f)). Qed.
Lemma lem3478609 {A B : Type'} (s : A -> Prop) (b : B) (g : type1413 A B) (x : A) : (term310 A B s b g x) = (term311 A B s b g x).
Proof. exact (@lem17362 (@IN A x s) (term269 A B b g x)). Qed.
Lemma lem3478614 {A B : Type'} (s : A -> Prop) (b : B) (g : type1413 A B) (x : A) : (term262 A B s b g x) = (term312 A B s b g x).
Proof. exact (@lem17265 (@IN A x s) (term269 A B b g x)). Qed.
Lemma lem3478615 {A : Type'} (P : A -> Prop) : (term276 A P) = (term277 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3478616 {A B : Type'} (s : A -> Prop) (b : B) (g : type1413 A B) : (term313 A B s b g) = (term314 A B s b g).
Proof. exact (@lem3478615 A (term263 A B s b g)). Qed.
Lemma lem3478617 {A B : Type'} (s : A -> Prop) (b : B) (g : type1413 A B) (x : A) : (term315 A B s b g x) = (term262 A B s b g x).
Proof. exact (eq_refl (term315 A B s b g x)). Qed.
Lemma lem3478618 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3478619 {A B : Type'} (s : A -> Prop) (b : B) (g : type1413 A B) (x : A) : (term316 A B s b g x) = (term310 A B s b g x).
Proof. exact (MK_COMB (@lem3478618) (@lem3478617 A B s b g x)). Qed.
Lemma lem3478620 {A B : Type'} (s : A -> Prop) (b : B) (g : type1413 A B) (x : A) : (term316 A B s b g x) = (term311 A B s b g x).
Proof. exact (TRANS (@lem3478619 A B s b g x) (@lem3478609 A B s b g x)). Qed.
Lemma lem3478621 {A B : Type'} (s : A -> Prop) (b : B) (g : type1413 A B) : (term317 A B s b g) = (term318 A B s b g).
Proof. exact (fun_ext (fun x : A => @lem3478620 A B s b g x)). Qed.
Lemma lem3478622 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3478623 {A B : Type'} (s : A -> Prop) (b : B) (g : type1413 A B) : (term314 A B s b g) = (term319 A B s b g).
Proof. exact (MK_COMB (@lem3478622 A) (@lem3478621 A B s b g)). Qed.
Lemma lem3478624 {A B : Type'} (s : A -> Prop) (b : B) (g : type1413 A B) : (term313 A B s b g) = (term319 A B s b g).
Proof. exact (TRANS (@lem3478616 A B s b g) (@lem3478623 A B s b g)). Qed.
Lemma lem3478625 {A B : Type'} (s : A -> Prop) (b : B) (g : type1413 A B) : (term263 A B s b g) = (term320 A B s b g).
Proof. exact (fun_ext (fun x : A => @lem3478614 A B s b g x)). Qed.
Lemma lem3478626 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3478627 {A B : Type'} (s : A -> Prop) (b : B) (g : type1413 A B) : (term181 A B s b g) = (term321 A B s b g).
Proof. exact (MK_COMB (@lem3478626 A) (@lem3478625 A B s b g)). Qed.
Lemma lem3478628 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3478629 {A B : Type'} (s : A -> Prop) (g : type1413 A B) (f : type1374 A B) : (term322 A B s g f) = (term323 A B s g f).
Proof. exact (MK_COMB (@lem3478628) (@lem3478597 A B s g f)). Qed.
Lemma lem3478630 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) (g : type1413 A B) : (term324 A B f s b g) = (term325 A B f s b g).
Proof. exact (MK_COMB (@lem3478629 A B s g f) (@lem3478624 A B s b g)). Qed.
Lemma lem3478631 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) (g : type1413 A B) : (term326 A B f s b g) = (term324 A B f s b g).
Proof. exact (@lem17045 (term99 A B s g f) (term181 A B s b g)). Qed.
Lemma lem3478632 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) (g : type1413 A B) : (term326 A B f s b g) = (term325 A B f s b g).
Proof. exact (TRANS (@lem3478631 A B f s b g) (@lem3478630 A B f s b g)). Qed.
Lemma lem3478633 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3478634 {A B : Type'} (s : A -> Prop) (g : type1413 A B) (f : type1374 A B) : (term117 A B s g f) = (term327 A B s g f).
Proof. exact (MK_COMB (@lem3478633) (@lem3478600 A B s g f)). Qed.
Lemma lem3478635 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) (g : type1413 A B) : (term195 A B f s b g) = (term328 A B f s b g).
Proof. exact (MK_COMB (@lem3478634 A B s g f) (@lem3478627 A B s b g)). Qed.
Lemma lem3478636 {A B : Type'} (P : type475 A B) : (term287 A B P) = (term288 A B P).
Proof. exact (@lem18394 (type1413 A B) P). Qed.
Lemma lem3478637 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : (term329 A B f s b) = (term330 A B f s b).
Proof. exact (@lem3478636 A B (term196 A B f s b)). Qed.
Lemma lem3478638 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) (g : type1413 A B) : (term331 A B f s b g) = (term195 A B f s b g).
Proof. exact (eq_refl (term331 A B f s b g)). Qed.
Lemma lem3478639 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3478640 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) (g : type1413 A B) : (term332 A B f s b g) = (term326 A B f s b g).
Proof. exact (MK_COMB (@lem3478639) (@lem3478638 A B f s b g)). Qed.
Lemma lem3478641 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) (g : type1413 A B) : (term332 A B f s b g) = (term325 A B f s b g).
Proof. exact (TRANS (@lem3478640 A B f s b g) (@lem3478632 A B f s b g)). Qed.
Lemma lem3478642 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : (term333 A B f s b) = (term334 A B f s b).
Proof. exact (fun_ext (fun g : type1413 A B => @lem3478641 A B f s b g)). Qed.
Lemma lem3478643 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem3478644 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : (term330 A B f s b) = (term335 A B f s b).
Proof. exact (MK_COMB (@lem3478643 A B) (@lem3478642 A B f s b)). Qed.
Lemma lem3478645 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : (term329 A B f s b) = (term335 A B f s b).
Proof. exact (TRANS (@lem3478637 A B f s b) (@lem3478644 A B f s b)). Qed.
Lemma lem3478646 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : (term196 A B f s b) = (term336 A B f s b).
Proof. exact (fun_ext (fun g : type1413 A B => @lem3478635 A B f s b g)). Qed.
Lemma lem3478647 {A B : Type'} : (@ex (A -> B -> Prop)) = (@ex (A -> B -> Prop)).
Proof. exact (eq_refl (@ex (A -> B -> Prop))). Qed.
Lemma lem3478648 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : (term197 A B f s b) = (term337 A B f s b).
Proof. exact (MK_COMB (@lem3478647 A B) (@lem3478646 A B f s b)). Qed.
Lemma lem3478649 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3478650 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) : (term338 A B s f b) = (term339 A B s f b).
Proof. exact (MK_COMB (@lem3478649) (@lem3478570 A B s f b)). Qed.
Lemma lem3478651 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : (term340 A B f s b) = (term341 A B f s b).
Proof. exact (MK_COMB (@lem3478650 A B s f b) (@lem3478648 A B f s b)). Qed.
Lemma lem3478652 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3478653 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) : (term342 A B s f b) = (term343 A B s f b).
Proof. exact (MK_COMB (@lem3478652) (@lem3478573 A B s f b)). Qed.
Lemma lem3478654 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : (term344 A B f s b) = (term345 A B f s b).
Proof. exact (MK_COMB (@lem3478653 A B s f b) (@lem3478645 A B f s b)). Qed.
Lemma lem3478655 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3478656 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : (term346 A B f s b) = (term347 A B f s b).
Proof. exact (MK_COMB (@lem3478655) (@lem3478654 A B f s b)). Qed.
Lemma lem3478657 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : (term348 A B f s b) = (term349 A B f s b).
Proof. exact (MK_COMB (@lem3478656 A B f s b) (@lem3478651 A B f s b)). Qed.
Lemma lem3478658 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : (term244 A B f s b) = (term348 A B f s b).
Proof. exact (@lem17646 (term240 A B s f b) (term197 A B f s b)). Qed.
Lemma lem3478659 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : (term244 A B f s b) = (term349 A B f s b).
Proof. exact (TRANS (@lem3478658 A B f s b) (@lem3478657 A B f s b)). Qed.
Lemma lem3479054 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term350 A P Q) = (term351 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3479055 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term350 A P Q) = (term351 A P Q).
Proof. exact (@lem3479054 A P Q). Qed.
Lemma lem3479056 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) (g : type1413 A B) : (term352 A B f s b g) = (term353 A B f s b g).
Proof. exact (@lem3479055 A (term306 A B s g f) (term318 A B s b g)). Qed.
Lemma lem3479057 {A B : Type'} (s : A -> Prop) (g : type1413 A B) (f : type1374 A B) (x : A) : (term354 A B s g f x) = (term299 A B s g f x).
Proof. exact (eq_refl (term354 A B s g f x)). Qed.
Lemma lem3479058 {A B : Type'} (s : A -> Prop) (g : type1413 A B) (f : type1374 A B) : (term355 A B s g f) = (term306 A B s g f).
Proof. exact (fun_ext (fun x : A => @lem3479057 A B s g f x)). Qed.
Lemma lem3479059 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3479060 {A B : Type'} (s : A -> Prop) (g : type1413 A B) (f : type1374 A B) : (term356 A B s g f) = (term307 A B s g f).
Proof. exact (MK_COMB (@lem3479059 A) (@lem3479058 A B s g f)). Qed.
Lemma lem3479061 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3479062 {A B : Type'} (s : A -> Prop) (g : type1413 A B) (f : type1374 A B) : (term357 A B s g f) = (term323 A B s g f).
Proof. exact (MK_COMB (@lem3479061) (@lem3479060 A B s g f)). Qed.
Lemma lem3479063 {A B : Type'} (s : A -> Prop) (b : B) (g : type1413 A B) (x : A) : (term358 A B s b g x) = (term311 A B s b g x).
Proof. exact (eq_refl (term358 A B s b g x)). Qed.
Lemma lem3479064 {A B : Type'} (s : A -> Prop) (b : B) (g : type1413 A B) : (term359 A B s b g) = (term318 A B s b g).
Proof. exact (fun_ext (fun x : A => @lem3479063 A B s b g x)). Qed.
Lemma lem3479065 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3479066 {A B : Type'} (s : A -> Prop) (b : B) (g : type1413 A B) : (term360 A B s b g) = (term319 A B s b g).
Proof. exact (MK_COMB (@lem3479065 A) (@lem3479064 A B s b g)). Qed.
Lemma lem3479067 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) (g : type1413 A B) : (term352 A B f s b g) = (term325 A B f s b g).
Proof. exact (MK_COMB (@lem3479062 A B s g f) (@lem3479066 A B s b g)). Qed.
Lemma lem3479068 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3479069 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) (g : type1413 A B) : (term361 A B f s b g) = (term362 A B f s b g).
Proof. exact (MK_COMB (@lem3479068) (@lem3479067 A B f s b g)). Qed.
Lemma lem3479070 {A B : Type'} (s : A -> Prop) (g : type1413 A B) (f : type1374 A B) (x : A) : (term354 A B s g f x) = (term299 A B s g f x).
Proof. exact (eq_refl (term354 A B s g f x)). Qed.
Lemma lem3479071 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3479072 {A B : Type'} (s : A -> Prop) (g : type1413 A B) (f : type1374 A B) (x : A) : (term363 A B s g f x) = (term364 A B s g f x).
Proof. exact (MK_COMB (@lem3479071) (@lem3479070 A B s g f x)). Qed.
Lemma lem3479073 {A B : Type'} (s : A -> Prop) (b : B) (g : type1413 A B) (x : A) : (term358 A B s b g x) = (term311 A B s b g x).
Proof. exact (eq_refl (term358 A B s b g x)). Qed.
Lemma lem3479074 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) (g : type1413 A B) (x : A) : (term365 A B f s b g x) = (term366 A B f s b g x).
Proof. exact (MK_COMB (@lem3479072 A B s g f x) (@lem3479073 A B s b g x)). Qed.
Lemma lem3479075 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) (g : type1413 A B) : (term367 A B f s b g) = (term368 A B f s b g).
Proof. exact (fun_ext (fun x : A => @lem3479074 A B f s b g x)). Qed.
Lemma lem3479076 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3479077 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) (g : type1413 A B) : (term353 A B f s b g) = (term369 A B f s b g).
Proof. exact (MK_COMB (@lem3479076 A) (@lem3479075 A B f s b g)). Qed.
Lemma lem3479078 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) (g : type1413 A B) : ((term352 A B f s b g) = (term353 A B f s b g)) = ((term325 A B f s b g) = (term369 A B f s b g)).
Proof. exact (MK_COMB (@lem3479069 A B f s b g) (@lem3479077 A B f s b g)). Qed.
Lemma lem3479079 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) (g : type1413 A B) : (term325 A B f s b g) = (term369 A B f s b g).
Proof. exact (EQ_MP (@lem3479078 A B f s b g) (@lem3479056 A B f s b g)). Qed.
Lemma lem3479080 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : (term334 A B f s b) = (term370 A B f s b).
Proof. exact (fun_ext (fun g : type1413 A B => @lem3479079 A B f s b g)). Qed.
Lemma lem3479081 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem3479082 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : (term335 A B f s b) = (term371 A B f s b).
Proof. exact (MK_COMB (@lem3479081 A B) (@lem3479080 A B f s b)). Qed.
Lemma lem3479084 {A B : Type'} (P : type1413 A B) : (term1 A B P) = (term2 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3479085 {A B : Type'} (P : type468 A B) : (term372 A B P) = (term373 A B P).
Proof. exact (@lem3479084 (type1413 A B) A P). Qed.
Lemma lem3479086 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : (term374 A B f s b) = (term375 A B f s b).
Proof. exact (@lem3479085 A B (term376 A B f s b)). Qed.
Lemma lem3479087 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) (g : type1413 A B) : (term377 A B f s b g) = (term368 A B f s b g).
Proof. exact (eq_refl (term377 A B f s b g)). Qed.
Lemma lem3479088 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3479089 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) (g : type1413 A B) (x : A) : (term378 A B f s b g x) = (term379 A B f s b g x).
Proof. exact (MK_COMB (@lem3479087 A B f s b g) (@lem3479088 A x)). Qed.
Lemma lem3479090 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) (g : type1413 A B) (x : A) : (term379 A B f s b g x) = (term366 A B f s b g x).
Proof. exact (eq_refl (term379 A B f s b g x)). Qed.
Lemma lem3479091 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) (g : type1413 A B) (x : A) : (term378 A B f s b g x) = (term366 A B f s b g x).
Proof. exact (TRANS (@lem3479089 A B f s b g x) (@lem3479090 A B f s b g x)). Qed.
Lemma lem3479092 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) (g : type1413 A B) : (term380 A B f s b g) = (term368 A B f s b g).
Proof. exact (fun_ext (fun x : A => @lem3479091 A B f s b g x)). Qed.
Lemma lem3479093 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3479094 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) (g : type1413 A B) : (term381 A B f s b g) = (term369 A B f s b g).
Proof. exact (MK_COMB (@lem3479093 A) (@lem3479092 A B f s b g)). Qed.
Lemma lem3479095 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : (term382 A B f s b) = (term370 A B f s b).
Proof. exact (fun_ext (fun g : type1413 A B => @lem3479094 A B f s b g)). Qed.
Lemma lem3479096 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem3479097 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : (term374 A B f s b) = (term371 A B f s b).
Proof. exact (MK_COMB (@lem3479096 A B) (@lem3479095 A B f s b)). Qed.
Lemma lem3479098 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3479099 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : (term383 A B f s b) = (term384 A B f s b).
Proof. exact (MK_COMB (@lem3479098) (@lem3479097 A B f s b)). Qed.
Lemma lem3479100 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) (g : type1413 A B) : (term377 A B f s b g) = (term368 A B f s b g).
Proof. exact (eq_refl (term377 A B f s b g)). Qed.
Lemma lem3479101 {A B : Type'} (x : type473 A B) (g : type1413 A B) : (x g) = (x g).
Proof. exact (eq_refl (x g)). Qed.
Lemma lem3479102 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) (x : type473 A B) (g : type1413 A B) : (term385 A B f s b x g) = (term386 A B f s b x g).
Proof. exact (MK_COMB (@lem3479100 A B f s b g) (@lem3479101 A B x g)). Qed.
Lemma lem3479103 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) (x : type473 A B) (g : type1413 A B) : (term386 A B f s b x g) = (term387 A B f s b x g).
Proof. exact (eq_refl (term386 A B f s b x g)). Qed.
Lemma lem3479104 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) (x : type473 A B) (g : type1413 A B) : (term385 A B f s b x g) = (term387 A B f s b x g).
Proof. exact (TRANS (@lem3479102 A B f s b x g) (@lem3479103 A B f s b x g)). Qed.
Lemma lem3479105 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) (x : type473 A B) : (term388 A B f s b x) = (term389 A B f s b x).
Proof. exact (fun_ext (fun g : type1413 A B => @lem3479104 A B f s b x g)). Qed.
Lemma lem3479106 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem3479107 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) (x : type473 A B) : (term390 A B f s b x) = (term391 A B f s b x).
Proof. exact (MK_COMB (@lem3479106 A B) (@lem3479105 A B f s b x)). Qed.
Lemma lem3479108 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : (term392 A B f s b) = (term393 A B f s b).
Proof. exact (fun_ext (fun x : type473 A B => @lem3479107 A B f s b x)). Qed.
Lemma lem3479109 {A B : Type'} : (@ex ((A -> B -> Prop) -> A)) = (@ex ((A -> B -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> B -> Prop) -> A))). Qed.
Lemma lem3479110 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : (term375 A B f s b) = (term394 A B f s b).
Proof. exact (MK_COMB (@lem3479109 A B) (@lem3479108 A B f s b)). Qed.
Lemma lem3479111 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : ((term374 A B f s b) = (term375 A B f s b)) = ((term371 A B f s b) = (term394 A B f s b)).
Proof. exact (MK_COMB (@lem3479099 A B f s b) (@lem3479110 A B f s b)). Qed.
Lemma lem3479112 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : (term371 A B f s b) = (term394 A B f s b).
Proof. exact (EQ_MP (@lem3479111 A B f s b) (@lem3479086 A B f s b)). Qed.
Lemma lem3479113 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : (term335 A B f s b) = (term394 A B f s b).
Proof. exact (TRANS (@lem3479082 A B f s b) (@lem3479112 A B f s b)). Qed.
Lemma lem3479114 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) : (term343 A B s f b) = (term343 A B s f b).
Proof. exact (eq_refl (term343 A B s f b)). Qed.
Lemma lem3479115 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : (term345 A B f s b) = (term395 A B f s b).
Proof. exact (MK_COMB (@lem3479114 A B s f b) (@lem3479113 A B f s b)). Qed.
Lemma lem3479117 {A : Type'} (P : A -> Prop) (Q : Prop) : (term396 A P Q) = (term397 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3479118 {A B : Type'} (P : type475 A B) (Q : Prop) : (term398 A B P Q) = (term399 A B P Q).
Proof. exact (@lem3479117 (type1413 A B) P Q). Qed.
Lemma lem3479119 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : (term400 A B f s b) = (term401 A B f s b).
Proof. exact (@lem3479118 A B (term296 A B s f b) (term394 A B f s b)). Qed.
Lemma lem3479120 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) (t : type1413 A B) : (term402 A B s f b t) = (term286 A B s f b t).
Proof. exact (eq_refl (term402 A B s f b t)). Qed.
Lemma lem3479121 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) : (term403 A B s f b) = (term296 A B s f b).
Proof. exact (fun_ext (fun t : type1413 A B => @lem3479120 A B s f b t)). Qed.
Lemma lem3479122 {A B : Type'} : (@ex (A -> B -> Prop)) = (@ex (A -> B -> Prop)).
Proof. exact (eq_refl (@ex (A -> B -> Prop))). Qed.
Lemma lem3479123 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) : (term404 A B s f b) = (term297 A B s f b).
Proof. exact (MK_COMB (@lem3479122 A B) (@lem3479121 A B s f b)). Qed.
Lemma lem3479124 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3479125 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) : (term405 A B s f b) = (term343 A B s f b).
Proof. exact (MK_COMB (@lem3479124) (@lem3479123 A B s f b)). Qed.
Lemma lem3479126 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : (term394 A B f s b) = (term394 A B f s b).
Proof. exact (eq_refl (term394 A B f s b)). Qed.
Lemma lem3479127 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : (term400 A B f s b) = (term395 A B f s b).
Proof. exact (MK_COMB (@lem3479125 A B s f b) (@lem3479126 A B f s b)). Qed.
Lemma lem3479128 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3479129 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : (term406 A B f s b) = (term407 A B f s b).
Proof. exact (MK_COMB (@lem3479128) (@lem3479127 A B f s b)). Qed.
Lemma lem3479130 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) (t : type1413 A B) : (term402 A B s f b t) = (term286 A B s f b t).
Proof. exact (eq_refl (term402 A B s f b t)). Qed.
Lemma lem3479131 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3479132 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) (t : type1413 A B) : (term408 A B s f b t) = (term409 A B s f b t).
Proof. exact (MK_COMB (@lem3479131) (@lem3479130 A B s f b t)). Qed.
Lemma lem3479133 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : (term394 A B f s b) = (term394 A B f s b).
Proof. exact (eq_refl (term394 A B f s b)). Qed.
Lemma lem3479134 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (b : B) : (term410 A B t f s b) = (term411 A B t f s b).
Proof. exact (MK_COMB (@lem3479132 A B s f b t) (@lem3479133 A B f s b)). Qed.
Lemma lem3479135 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : (term412 A B f s b) = (term413 A B f s b).
Proof. exact (fun_ext (fun t : type1413 A B => @lem3479134 A B t f s b)). Qed.
Lemma lem3479136 {A B : Type'} : (@ex (A -> B -> Prop)) = (@ex (A -> B -> Prop)).
Proof. exact (eq_refl (@ex (A -> B -> Prop))). Qed.
Lemma lem3479137 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : (term401 A B f s b) = (term414 A B f s b).
Proof. exact (MK_COMB (@lem3479136 A B) (@lem3479135 A B f s b)). Qed.
Lemma lem3479138 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : ((term400 A B f s b) = (term401 A B f s b)) = ((term395 A B f s b) = (term414 A B f s b)).
Proof. exact (MK_COMB (@lem3479129 A B f s b) (@lem3479137 A B f s b)). Qed.
Lemma lem3479139 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : (term395 A B f s b) = (term414 A B f s b).
Proof. exact (EQ_MP (@lem3479138 A B f s b) (@lem3479119 A B f s b)). Qed.
Lemma lem3479141 {A : Type'} (P : Prop) (Q : A -> Prop) : (term415 A P Q) = (term416 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3479142 {A B : Type'} (P : Prop) (Q : type89 A B) : (term417 A B P Q) = (term418 A B P Q).
Proof. exact (@lem3479141 (type473 A B) P Q). Qed.
Lemma lem3479143 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (b : B) : (term419 A B t f s b) = (term420 A B t f s b).
Proof. exact (@lem3479142 A B (term286 A B s f b t) (term393 A B f s b)). Qed.
Lemma lem3479144 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) (x : type473 A B) : (term421 A B f s b x) = (term391 A B f s b x).
Proof. exact (eq_refl (term421 A B f s b x)). Qed.
Lemma lem3479145 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : (term422 A B f s b) = (term393 A B f s b).
Proof. exact (fun_ext (fun x : type473 A B => @lem3479144 A B f s b x)). Qed.
Lemma lem3479146 {A B : Type'} : (@ex ((A -> B -> Prop) -> A)) = (@ex ((A -> B -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> B -> Prop) -> A))). Qed.
Lemma lem3479147 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : (term423 A B f s b) = (term394 A B f s b).
Proof. exact (MK_COMB (@lem3479146 A B) (@lem3479145 A B f s b)). Qed.
Lemma lem3479148 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) (t : type1413 A B) : (term409 A B s f b t) = (term409 A B s f b t).
Proof. exact (eq_refl (term409 A B s f b t)). Qed.
Lemma lem3479149 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (b : B) : (term419 A B t f s b) = (term411 A B t f s b).
Proof. exact (MK_COMB (@lem3479148 A B s f b t) (@lem3479147 A B f s b)). Qed.
Lemma lem3479150 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3479151 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (b : B) : (term424 A B t f s b) = (term425 A B t f s b).
Proof. exact (MK_COMB (@lem3479150) (@lem3479149 A B t f s b)). Qed.
Lemma lem3479152 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) (x : type473 A B) : (term421 A B f s b x) = (term391 A B f s b x).
Proof. exact (eq_refl (term421 A B f s b x)). Qed.
Lemma lem3479153 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) (t : type1413 A B) : (term409 A B s f b t) = (term409 A B s f b t).
Proof. exact (eq_refl (term409 A B s f b t)). Qed.
Lemma lem3479154 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (x : type473 A B) : (term426 A B t f s b x) = (term427 A B t f s b x).
Proof. exact (MK_COMB (@lem3479153 A B s f b t) (@lem3479152 A B f s b x)). Qed.
Lemma lem3479155 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (b : B) : (term428 A B t f s b) = (term429 A B t f s b).
Proof. exact (fun_ext (fun x : type473 A B => @lem3479154 A B t f s b x)). Qed.
Lemma lem3479156 {A B : Type'} : (@ex ((A -> B -> Prop) -> A)) = (@ex ((A -> B -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> B -> Prop) -> A))). Qed.
Lemma lem3479157 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (b : B) : (term420 A B t f s b) = (term430 A B t f s b).
Proof. exact (MK_COMB (@lem3479156 A B) (@lem3479155 A B t f s b)). Qed.
Lemma lem3479158 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (b : B) : ((term419 A B t f s b) = (term420 A B t f s b)) = ((term411 A B t f s b) = (term430 A B t f s b)).
Proof. exact (MK_COMB (@lem3479151 A B t f s b) (@lem3479157 A B t f s b)). Qed.
Lemma lem3479159 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (b : B) : (term411 A B t f s b) = (term430 A B t f s b).
Proof. exact (EQ_MP (@lem3479158 A B t f s b) (@lem3479143 A B t f s b)). Qed.
Lemma lem3479160 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : (term413 A B f s b) = (term431 A B f s b).
Proof. exact (fun_ext (fun t : type1413 A B => @lem3479159 A B t f s b)). Qed.
Lemma lem3479161 {A B : Type'} : (@ex (A -> B -> Prop)) = (@ex (A -> B -> Prop)).
Proof. exact (eq_refl (@ex (A -> B -> Prop))). Qed.
Lemma lem3479162 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : (term414 A B f s b) = (term432 A B f s b).
Proof. exact (MK_COMB (@lem3479161 A B) (@lem3479160 A B f s b)). Qed.
Lemma lem3479163 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : (term395 A B f s b) = (term432 A B f s b).
Proof. exact (TRANS (@lem3479139 A B f s b) (@lem3479162 A B f s b)). Qed.
Lemma lem3479164 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : (term345 A B f s b) = (term432 A B f s b).
Proof. exact (TRANS (@lem3479115 A B f s b) (@lem3479163 A B f s b)). Qed.
Lemma lem3479165 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3479166 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : (term347 A B f s b) = (term433 A B f s b).
Proof. exact (MK_COMB (@lem3479165) (@lem3479164 A B f s b)). Qed.
Lemma lem3479168 {A B : Type'} (P : type1413 A B) : (term1 A B P) = (term2 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3479169 {A B : Type'} (P : type468 A B) : (term372 A B P) = (term373 A B P).
Proof. exact (@lem3479168 (type1413 A B) A P). Qed.
Lemma lem3479170 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) : (term434 A B s f b) = (term435 A B s f b).
Proof. exact (@lem3479169 A B (term436 A B s f b)). Qed.
Lemma lem3479171 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) (t : type1413 A B) : (term437 A B s f b t) = (term283 A B s f b t).
Proof. exact (eq_refl (term437 A B s f b t)). Qed.
Lemma lem3479172 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3479173 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) (t : type1413 A B) (x : A) : (term438 A B s f b t x) = (term439 A B s f b t x).
Proof. exact (MK_COMB (@lem3479171 A B s f b t) (@lem3479172 A x)). Qed.
Lemma lem3479174 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) (t : type1413 A B) (x : A) : (term439 A B s f b t x) = (term272 A B s f b t x).
Proof. exact (eq_refl (term439 A B s f b t x)). Qed.
Lemma lem3479175 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) (t : type1413 A B) (x : A) : (term438 A B s f b t x) = (term272 A B s f b t x).
Proof. exact (TRANS (@lem3479173 A B s f b t x) (@lem3479174 A B s f b t x)). Qed.
Lemma lem3479176 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) (t : type1413 A B) : (term440 A B s f b t) = (term283 A B s f b t).
Proof. exact (fun_ext (fun x : A => @lem3479175 A B s f b t x)). Qed.
Lemma lem3479177 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3479178 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) (t : type1413 A B) : (term441 A B s f b t) = (term284 A B s f b t).
Proof. exact (MK_COMB (@lem3479177 A) (@lem3479176 A B s f b t)). Qed.
Lemma lem3479179 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) : (term442 A B s f b) = (term294 A B s f b).
Proof. exact (fun_ext (fun t : type1413 A B => @lem3479178 A B s f b t)). Qed.
Lemma lem3479180 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem3479181 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) : (term434 A B s f b) = (term295 A B s f b).
Proof. exact (MK_COMB (@lem3479180 A B) (@lem3479179 A B s f b)). Qed.
Lemma lem3479182 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3479183 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) : (term443 A B s f b) = (term444 A B s f b).
Proof. exact (MK_COMB (@lem3479182) (@lem3479181 A B s f b)). Qed.
Lemma lem3479184 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) (t : type1413 A B) : (term437 A B s f b t) = (term283 A B s f b t).
Proof. exact (eq_refl (term437 A B s f b t)). Qed.
Lemma lem3479185 {A B : Type'} (x : type473 A B) (t : type1413 A B) : (x t) = (x t).
Proof. exact (eq_refl (x t)). Qed.
Lemma lem3479186 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) (x : type473 A B) (t : type1413 A B) : (term445 A B s f b x t) = (term446 A B s f b x t).
Proof. exact (MK_COMB (@lem3479184 A B s f b t) (@lem3479185 A B x t)). Qed.
Lemma lem3479187 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) (x : type473 A B) (t : type1413 A B) : (term446 A B s f b x t) = (term447 A B s f b x t).
Proof. exact (eq_refl (term446 A B s f b x t)). Qed.
Lemma lem3479188 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) (x : type473 A B) (t : type1413 A B) : (term445 A B s f b x t) = (term447 A B s f b x t).
Proof. exact (TRANS (@lem3479186 A B s f b x t) (@lem3479187 A B s f b x t)). Qed.
Lemma lem3479189 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) (x : type473 A B) : (term448 A B s f b x) = (term449 A B s f b x).
Proof. exact (fun_ext (fun t : type1413 A B => @lem3479188 A B s f b x t)). Qed.
Lemma lem3479190 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem3479191 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) (x : type473 A B) : (term450 A B s f b x) = (term451 A B s f b x).
Proof. exact (MK_COMB (@lem3479190 A B) (@lem3479189 A B s f b x)). Qed.
Lemma lem3479192 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) : (term452 A B s f b) = (term453 A B s f b).
Proof. exact (fun_ext (fun x : type473 A B => @lem3479191 A B s f b x)). Qed.
Lemma lem3479193 {A B : Type'} : (@ex ((A -> B -> Prop) -> A)) = (@ex ((A -> B -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> B -> Prop) -> A))). Qed.
Lemma lem3479194 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) : (term435 A B s f b) = (term454 A B s f b).
Proof. exact (MK_COMB (@lem3479193 A B) (@lem3479192 A B s f b)). Qed.
Lemma lem3479195 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) : ((term434 A B s f b) = (term435 A B s f b)) = ((term295 A B s f b) = (term454 A B s f b)).
Proof. exact (MK_COMB (@lem3479183 A B s f b) (@lem3479194 A B s f b)). Qed.
Lemma lem3479196 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) : (term295 A B s f b) = (term454 A B s f b).
Proof. exact (EQ_MP (@lem3479195 A B s f b) (@lem3479170 A B s f b)). Qed.
Lemma lem3479197 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3479198 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) : (term339 A B s f b) = (term455 A B s f b).
Proof. exact (MK_COMB (@lem3479197) (@lem3479196 A B s f b)). Qed.
Lemma lem3479199 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : (term337 A B f s b) = (term337 A B f s b).
Proof. exact (eq_refl (term337 A B f s b)). Qed.
Lemma lem3479200 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : (term341 A B f s b) = (term456 A B f s b).
Proof. exact (MK_COMB (@lem3479198 A B s f b) (@lem3479199 A B f s b)). Qed.
Lemma lem3479202 {A : Type'} (P : A -> Prop) (Q : Prop) : (term396 A P Q) = (term397 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3479203 {A B : Type'} (P : type89 A B) (Q : Prop) : (term457 A B P Q) = (term458 A B P Q).
Proof. exact (@lem3479202 (type473 A B) P Q). Qed.
Lemma lem3479204 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : (term459 A B f s b) = (term460 A B f s b).
Proof. exact (@lem3479203 A B (term453 A B s f b) (term337 A B f s b)). Qed.
Lemma lem3479205 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) (x : type473 A B) : (term461 A B s f b x) = (term451 A B s f b x).
Proof. exact (eq_refl (term461 A B s f b x)). Qed.
Lemma lem3479206 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) : (term462 A B s f b) = (term453 A B s f b).
Proof. exact (fun_ext (fun x : type473 A B => @lem3479205 A B s f b x)). Qed.
Lemma lem3479207 {A B : Type'} : (@ex ((A -> B -> Prop) -> A)) = (@ex ((A -> B -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> B -> Prop) -> A))). Qed.
Lemma lem3479208 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) : (term463 A B s f b) = (term454 A B s f b).
Proof. exact (MK_COMB (@lem3479207 A B) (@lem3479206 A B s f b)). Qed.
Lemma lem3479209 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3479210 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) : (term464 A B s f b) = (term455 A B s f b).
Proof. exact (MK_COMB (@lem3479209) (@lem3479208 A B s f b)). Qed.
Lemma lem3479211 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : (term337 A B f s b) = (term337 A B f s b).
Proof. exact (eq_refl (term337 A B f s b)). Qed.
Lemma lem3479212 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : (term459 A B f s b) = (term456 A B f s b).
Proof. exact (MK_COMB (@lem3479210 A B s f b) (@lem3479211 A B f s b)). Qed.
Lemma lem3479213 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3479214 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : (term465 A B f s b) = (term466 A B f s b).
Proof. exact (MK_COMB (@lem3479213) (@lem3479212 A B f s b)). Qed.
Lemma lem3479215 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) (x : type473 A B) : (term461 A B s f b x) = (term451 A B s f b x).
Proof. exact (eq_refl (term461 A B s f b x)). Qed.
Lemma lem3479216 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3479217 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) (x : type473 A B) : (term467 A B s f b x) = (term468 A B s f b x).
Proof. exact (MK_COMB (@lem3479216) (@lem3479215 A B s f b x)). Qed.
Lemma lem3479218 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : (term337 A B f s b) = (term337 A B f s b).
Proof. exact (eq_refl (term337 A B f s b)). Qed.
Lemma lem3479219 {A B : Type'} (x : type473 A B) (f : type1374 A B) (s : A -> Prop) (b : B) : (term469 A B x f s b) = (term470 A B x f s b).
Proof. exact (MK_COMB (@lem3479217 A B s f b x) (@lem3479218 A B f s b)). Qed.
Lemma lem3479220 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : (term471 A B f s b) = (term472 A B f s b).
Proof. exact (fun_ext (fun x : type473 A B => @lem3479219 A B x f s b)). Qed.
Lemma lem3479221 {A B : Type'} : (@ex ((A -> B -> Prop) -> A)) = (@ex ((A -> B -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> B -> Prop) -> A))). Qed.
Lemma lem3479222 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : (term460 A B f s b) = (term473 A B f s b).
Proof. exact (MK_COMB (@lem3479221 A B) (@lem3479220 A B f s b)). Qed.
Lemma lem3479223 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : ((term459 A B f s b) = (term460 A B f s b)) = ((term456 A B f s b) = (term473 A B f s b)).
Proof. exact (MK_COMB (@lem3479214 A B f s b) (@lem3479222 A B f s b)). Qed.
Lemma lem3479224 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : (term456 A B f s b) = (term473 A B f s b).
Proof. exact (EQ_MP (@lem3479223 A B f s b) (@lem3479204 A B f s b)). Qed.
Lemma lem3479226 {A : Type'} (P : Prop) (Q : A -> Prop) : (term415 A P Q) = (term416 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3479227 {A B : Type'} (P : Prop) (Q : type475 A B) : (term474 A B P Q) = (term475 A B P Q).
Proof. exact (@lem3479226 (type1413 A B) P Q). Qed.
Lemma lem3479228 {A B : Type'} (x : type473 A B) (f : type1374 A B) (s : A -> Prop) (b : B) : (term476 A B x f s b) = (term477 A B x f s b).
Proof. exact (@lem3479227 A B (term451 A B s f b x) (term336 A B f s b)). Qed.
Lemma lem3479229 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) (g : type1413 A B) : (term478 A B f s b g) = (term328 A B f s b g).
Proof. exact (eq_refl (term478 A B f s b g)). Qed.
Lemma lem3479230 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : (term479 A B f s b) = (term336 A B f s b).
Proof. exact (fun_ext (fun g : type1413 A B => @lem3479229 A B f s b g)). Qed.
Lemma lem3479231 {A B : Type'} : (@ex (A -> B -> Prop)) = (@ex (A -> B -> Prop)).
Proof. exact (eq_refl (@ex (A -> B -> Prop))). Qed.
Lemma lem3479232 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : (term480 A B f s b) = (term337 A B f s b).
Proof. exact (MK_COMB (@lem3479231 A B) (@lem3479230 A B f s b)). Qed.
Lemma lem3479233 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) (x : type473 A B) : (term468 A B s f b x) = (term468 A B s f b x).
Proof. exact (eq_refl (term468 A B s f b x)). Qed.
Lemma lem3479234 {A B : Type'} (x : type473 A B) (f : type1374 A B) (s : A -> Prop) (b : B) : (term476 A B x f s b) = (term470 A B x f s b).
Proof. exact (MK_COMB (@lem3479233 A B s f b x) (@lem3479232 A B f s b)). Qed.
Lemma lem3479235 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3479236 {A B : Type'} (x : type473 A B) (f : type1374 A B) (s : A -> Prop) (b : B) : (term481 A B x f s b) = (term482 A B x f s b).
Proof. exact (MK_COMB (@lem3479235) (@lem3479234 A B x f s b)). Qed.
Lemma lem3479237 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) (g : type1413 A B) : (term478 A B f s b g) = (term328 A B f s b g).
Proof. exact (eq_refl (term478 A B f s b g)). Qed.
Lemma lem3479238 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) (x : type473 A B) : (term468 A B s f b x) = (term468 A B s f b x).
Proof. exact (eq_refl (term468 A B s f b x)). Qed.
Lemma lem3479239 {A B : Type'} (x : type473 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (g : type1413 A B) : (term483 A B x f s b g) = (term484 A B x f s b g).
Proof. exact (MK_COMB (@lem3479238 A B s f b x) (@lem3479237 A B f s b g)). Qed.
Lemma lem3479240 {A B : Type'} (x : type473 A B) (f : type1374 A B) (s : A -> Prop) (b : B) : (term485 A B x f s b) = (term486 A B x f s b).
Proof. exact (fun_ext (fun g : type1413 A B => @lem3479239 A B x f s b g)). Qed.
Lemma lem3479241 {A B : Type'} : (@ex (A -> B -> Prop)) = (@ex (A -> B -> Prop)).
Proof. exact (eq_refl (@ex (A -> B -> Prop))). Qed.
Lemma lem3479242 {A B : Type'} (x : type473 A B) (f : type1374 A B) (s : A -> Prop) (b : B) : (term477 A B x f s b) = (term487 A B x f s b).
Proof. exact (MK_COMB (@lem3479241 A B) (@lem3479240 A B x f s b)). Qed.
Lemma lem3479243 {A B : Type'} (x : type473 A B) (f : type1374 A B) (s : A -> Prop) (b : B) : ((term476 A B x f s b) = (term477 A B x f s b)) = ((term470 A B x f s b) = (term487 A B x f s b)).
Proof. exact (MK_COMB (@lem3479236 A B x f s b) (@lem3479242 A B x f s b)). Qed.
Lemma lem3479244 {A B : Type'} (x : type473 A B) (f : type1374 A B) (s : A -> Prop) (b : B) : (term470 A B x f s b) = (term487 A B x f s b).
Proof. exact (EQ_MP (@lem3479243 A B x f s b) (@lem3479228 A B x f s b)). Qed.
Lemma lem3479245 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : (term472 A B f s b) = (term488 A B f s b).
Proof. exact (fun_ext (fun x : type473 A B => @lem3479244 A B x f s b)). Qed.
Lemma lem3479246 {A B : Type'} : (@ex ((A -> B -> Prop) -> A)) = (@ex ((A -> B -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> B -> Prop) -> A))). Qed.
Lemma lem3479247 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : (term473 A B f s b) = (term489 A B f s b).
Proof. exact (MK_COMB (@lem3479246 A B) (@lem3479245 A B f s b)). Qed.
Lemma lem3479248 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : (term456 A B f s b) = (term489 A B f s b).
Proof. exact (TRANS (@lem3479224 A B f s b) (@lem3479247 A B f s b)). Qed.
Lemma lem3479249 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : (term341 A B f s b) = (term489 A B f s b).
Proof. exact (TRANS (@lem3479200 A B f s b) (@lem3479248 A B f s b)). Qed.
Lemma lem3479250 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : (term349 A B f s b) = (term490 A B f s b).
Proof. exact (MK_COMB (@lem3479166 A B f s b) (@lem3479249 A B f s b)). Qed.
Lemma lem3479254 {A : Type'} (P : A -> Prop) (Q : Prop) : (term491 A P Q) = (term492 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3479255 {A B : Type'} (P : type475 A B) (Q : Prop) : (term493 A B P Q) = (term494 A B P Q).
Proof. exact (@lem3479254 (type1413 A B) P Q). Qed.
Lemma lem3479256 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : (term495 A B f s b) = (term496 A B f s b).
Proof. exact (@lem3479255 A B (term431 A B f s b) (term489 A B f s b)). Qed.
Lemma lem3479257 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (b : B) : (term497 A B f s b t) = (term430 A B t f s b).
Proof. exact (eq_refl (term497 A B f s b t)). Qed.
Lemma lem3479258 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : (term498 A B f s b) = (term431 A B f s b).
Proof. exact (fun_ext (fun t : type1413 A B => @lem3479257 A B t f s b)). Qed.
Lemma lem3479259 {A B : Type'} : (@ex (A -> B -> Prop)) = (@ex (A -> B -> Prop)).
Proof. exact (eq_refl (@ex (A -> B -> Prop))). Qed.
Lemma lem3479260 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : (term499 A B f s b) = (term432 A B f s b).
Proof. exact (MK_COMB (@lem3479259 A B) (@lem3479258 A B f s b)). Qed.
Lemma lem3479261 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3479262 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : (term500 A B f s b) = (term433 A B f s b).
Proof. exact (MK_COMB (@lem3479261) (@lem3479260 A B f s b)). Qed.
Lemma lem3479263 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : (term489 A B f s b) = (term489 A B f s b).
Proof. exact (eq_refl (term489 A B f s b)). Qed.
Lemma lem3479264 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : (term495 A B f s b) = (term490 A B f s b).
Proof. exact (MK_COMB (@lem3479262 A B f s b) (@lem3479263 A B f s b)). Qed.
Lemma lem3479265 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3479266 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : (term501 A B f s b) = (term502 A B f s b).
Proof. exact (MK_COMB (@lem3479265) (@lem3479264 A B f s b)). Qed.
Lemma lem3479267 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (b : B) : (term497 A B f s b t) = (term430 A B t f s b).
Proof. exact (eq_refl (term497 A B f s b t)). Qed.
Lemma lem3479268 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3479269 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (b : B) : (term503 A B f s b t) = (term504 A B t f s b).
Proof. exact (MK_COMB (@lem3479268) (@lem3479267 A B t f s b)). Qed.
Lemma lem3479270 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : (term489 A B f s b) = (term489 A B f s b).
Proof. exact (eq_refl (term489 A B f s b)). Qed.
Lemma lem3479271 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (b : B) : (term505 A B t f s b) = (term506 A B t f s b).
Proof. exact (MK_COMB (@lem3479269 A B t f s b) (@lem3479270 A B f s b)). Qed.
Lemma lem3479272 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : (term507 A B f s b) = (term508 A B f s b).
Proof. exact (fun_ext (fun t : type1413 A B => @lem3479271 A B t f s b)). Qed.
Lemma lem3479273 {A B : Type'} : (@ex (A -> B -> Prop)) = (@ex (A -> B -> Prop)).
Proof. exact (eq_refl (@ex (A -> B -> Prop))). Qed.
Lemma lem3479274 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : (term496 A B f s b) = (term509 A B f s b).
Proof. exact (MK_COMB (@lem3479273 A B) (@lem3479272 A B f s b)). Qed.
Lemma lem3479275 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : ((term495 A B f s b) = (term496 A B f s b)) = ((term490 A B f s b) = (term509 A B f s b)).
Proof. exact (MK_COMB (@lem3479266 A B f s b) (@lem3479274 A B f s b)). Qed.
Lemma lem3479276 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : (term490 A B f s b) = (term509 A B f s b).
Proof. exact (EQ_MP (@lem3479275 A B f s b) (@lem3479256 A B f s b)). Qed.
Lemma lem3479278 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term350 A P Q) = (term351 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3479279 {A B : Type'} (P : type89 A B) (Q : type89 A B) : (term510 A B P Q) = (term511 A B P Q).
Proof. exact (@lem3479278 (type473 A B) P Q). Qed.
Lemma lem3479280 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (b : B) : (term512 A B t f s b) = (term513 A B t f s b).
Proof. exact (@lem3479279 A B (term429 A B t f s b) (term488 A B f s b)). Qed.
Lemma lem3479281 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (x : type473 A B) : (term514 A B t f s b x) = (term427 A B t f s b x).
Proof. exact (eq_refl (term514 A B t f s b x)). Qed.
Lemma lem3479282 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (b : B) : (term515 A B t f s b) = (term429 A B t f s b).
Proof. exact (fun_ext (fun x : type473 A B => @lem3479281 A B t f s b x)). Qed.
Lemma lem3479283 {A B : Type'} : (@ex ((A -> B -> Prop) -> A)) = (@ex ((A -> B -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> B -> Prop) -> A))). Qed.
Lemma lem3479284 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (b : B) : (term516 A B t f s b) = (term430 A B t f s b).
Proof. exact (MK_COMB (@lem3479283 A B) (@lem3479282 A B t f s b)). Qed.
Lemma lem3479285 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3479286 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (b : B) : (term517 A B t f s b) = (term504 A B t f s b).
Proof. exact (MK_COMB (@lem3479285) (@lem3479284 A B t f s b)). Qed.
Lemma lem3479287 {A B : Type'} (x : type473 A B) (f : type1374 A B) (s : A -> Prop) (b : B) : (term518 A B f s b x) = (term487 A B x f s b).
Proof. exact (eq_refl (term518 A B f s b x)). Qed.
Lemma lem3479288 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : (term519 A B f s b) = (term488 A B f s b).
Proof. exact (fun_ext (fun x : type473 A B => @lem3479287 A B x f s b)). Qed.
Lemma lem3479289 {A B : Type'} : (@ex ((A -> B -> Prop) -> A)) = (@ex ((A -> B -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> B -> Prop) -> A))). Qed.
Lemma lem3479290 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : (term520 A B f s b) = (term489 A B f s b).
Proof. exact (MK_COMB (@lem3479289 A B) (@lem3479288 A B f s b)). Qed.
Lemma lem3479291 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (b : B) : (term512 A B t f s b) = (term506 A B t f s b).
Proof. exact (MK_COMB (@lem3479286 A B t f s b) (@lem3479290 A B f s b)). Qed.
Lemma lem3479292 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3479293 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (b : B) : (term521 A B t f s b) = (term522 A B t f s b).
Proof. exact (MK_COMB (@lem3479292) (@lem3479291 A B t f s b)). Qed.
Lemma lem3479294 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (x : type473 A B) : (term514 A B t f s b x) = (term427 A B t f s b x).
Proof. exact (eq_refl (term514 A B t f s b x)). Qed.
Lemma lem3479295 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3479296 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (x : type473 A B) : (term523 A B t f s b x) = (term524 A B t f s b x).
Proof. exact (MK_COMB (@lem3479295) (@lem3479294 A B t f s b x)). Qed.
Lemma lem3479297 {A B : Type'} (x : type473 A B) (f : type1374 A B) (s : A -> Prop) (b : B) : (term518 A B f s b x) = (term487 A B x f s b).
Proof. exact (eq_refl (term518 A B f s b x)). Qed.
Lemma lem3479298 {A B : Type'} (t : type1413 A B) (x : type473 A B) (f : type1374 A B) (s : A -> Prop) (b : B) : (term525 A B t f s b x) = (term526 A B t x f s b).
Proof. exact (MK_COMB (@lem3479296 A B t f s b x) (@lem3479297 A B x f s b)). Qed.
Lemma lem3479299 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (b : B) : (term527 A B t f s b) = (term528 A B t f s b).
Proof. exact (fun_ext (fun x : type473 A B => @lem3479298 A B t x f s b)). Qed.
Lemma lem3479300 {A B : Type'} : (@ex ((A -> B -> Prop) -> A)) = (@ex ((A -> B -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> B -> Prop) -> A))). Qed.
Lemma lem3479301 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (b : B) : (term513 A B t f s b) = (term529 A B t f s b).
Proof. exact (MK_COMB (@lem3479300 A B) (@lem3479299 A B t f s b)). Qed.
Lemma lem3479302 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (b : B) : ((term512 A B t f s b) = (term513 A B t f s b)) = ((term506 A B t f s b) = (term529 A B t f s b)).
Proof. exact (MK_COMB (@lem3479293 A B t f s b) (@lem3479301 A B t f s b)). Qed.
Lemma lem3479303 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (b : B) : (term506 A B t f s b) = (term529 A B t f s b).
Proof. exact (EQ_MP (@lem3479302 A B t f s b) (@lem3479280 A B t f s b)). Qed.
Lemma lem3479305 {A : Type'} (P : Prop) (Q : A -> Prop) : (term530 A P Q) = (term531 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3479306 {A B : Type'} (P : Prop) (Q : type475 A B) : (term532 A B P Q) = (term533 A B P Q).
Proof. exact (@lem3479305 (type1413 A B) P Q). Qed.
Lemma lem3479307 {A B : Type'} (t : type1413 A B) (x : type473 A B) (f : type1374 A B) (s : A -> Prop) (b : B) : (term534 A B t x f s b) = (term535 A B t x f s b).
Proof. exact (@lem3479306 A B (term427 A B t f s b x) (term486 A B x f s b)). Qed.
Lemma lem3479308 {A B : Type'} (x : type473 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (g : type1413 A B) : (term536 A B x f s b g) = (term484 A B x f s b g).
Proof. exact (eq_refl (term536 A B x f s b g)). Qed.
Lemma lem3479309 {A B : Type'} (x : type473 A B) (f : type1374 A B) (s : A -> Prop) (b : B) : (term537 A B x f s b) = (term486 A B x f s b).
Proof. exact (fun_ext (fun g : type1413 A B => @lem3479308 A B x f s b g)). Qed.
Lemma lem3479310 {A B : Type'} : (@ex (A -> B -> Prop)) = (@ex (A -> B -> Prop)).
Proof. exact (eq_refl (@ex (A -> B -> Prop))). Qed.
Lemma lem3479311 {A B : Type'} (x : type473 A B) (f : type1374 A B) (s : A -> Prop) (b : B) : (term538 A B x f s b) = (term487 A B x f s b).
Proof. exact (MK_COMB (@lem3479310 A B) (@lem3479309 A B x f s b)). Qed.
Lemma lem3479312 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (x : type473 A B) : (term524 A B t f s b x) = (term524 A B t f s b x).
Proof. exact (eq_refl (term524 A B t f s b x)). Qed.
Lemma lem3479313 {A B : Type'} (t : type1413 A B) (x : type473 A B) (f : type1374 A B) (s : A -> Prop) (b : B) : (term534 A B t x f s b) = (term526 A B t x f s b).
Proof. exact (MK_COMB (@lem3479312 A B t f s b x) (@lem3479311 A B x f s b)). Qed.
Lemma lem3479314 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3479315 {A B : Type'} (t : type1413 A B) (x : type473 A B) (f : type1374 A B) (s : A -> Prop) (b : B) : (term539 A B t x f s b) = (term540 A B t x f s b).
Proof. exact (MK_COMB (@lem3479314) (@lem3479313 A B t x f s b)). Qed.
Lemma lem3479316 {A B : Type'} (x : type473 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (g : type1413 A B) : (term536 A B x f s b g) = (term484 A B x f s b g).
Proof. exact (eq_refl (term536 A B x f s b g)). Qed.
Lemma lem3479317 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (x : type473 A B) : (term524 A B t f s b x) = (term524 A B t f s b x).
Proof. exact (eq_refl (term524 A B t f s b x)). Qed.
Lemma lem3479318 {A B : Type'} (t : type1413 A B) (x : type473 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (g : type1413 A B) : (term541 A B t x f s b g) = (term542 A B t x f s b g).
Proof. exact (MK_COMB (@lem3479317 A B t f s b x) (@lem3479316 A B x f s b g)). Qed.
Lemma lem3479319 {A B : Type'} (t : type1413 A B) (x : type473 A B) (f : type1374 A B) (s : A -> Prop) (b : B) : (term543 A B t x f s b) = (term544 A B t x f s b).
Proof. exact (fun_ext (fun g : type1413 A B => @lem3479318 A B t x f s b g)). Qed.
Lemma lem3479320 {A B : Type'} : (@ex (A -> B -> Prop)) = (@ex (A -> B -> Prop)).
Proof. exact (eq_refl (@ex (A -> B -> Prop))). Qed.
Lemma lem3479321 {A B : Type'} (t : type1413 A B) (x : type473 A B) (f : type1374 A B) (s : A -> Prop) (b : B) : (term535 A B t x f s b) = (term545 A B t x f s b).
Proof. exact (MK_COMB (@lem3479320 A B) (@lem3479319 A B t x f s b)). Qed.
Lemma lem3479322 {A B : Type'} (t : type1413 A B) (x : type473 A B) (f : type1374 A B) (s : A -> Prop) (b : B) : ((term534 A B t x f s b) = (term535 A B t x f s b)) = ((term526 A B t x f s b) = (term545 A B t x f s b)).
Proof. exact (MK_COMB (@lem3479315 A B t x f s b) (@lem3479321 A B t x f s b)). Qed.
Lemma lem3479323 {A B : Type'} (t : type1413 A B) (x : type473 A B) (f : type1374 A B) (s : A -> Prop) (b : B) : (term526 A B t x f s b) = (term545 A B t x f s b).
Proof. exact (EQ_MP (@lem3479322 A B t x f s b) (@lem3479307 A B t x f s b)). Qed.
Lemma lem3479324 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (b : B) : (term528 A B t f s b) = (term546 A B t f s b).
Proof. exact (fun_ext (fun x : type473 A B => @lem3479323 A B t x f s b)). Qed.
Lemma lem3479325 {A B : Type'} : (@ex ((A -> B -> Prop) -> A)) = (@ex ((A -> B -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> B -> Prop) -> A))). Qed.
Lemma lem3479326 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (b : B) : (term529 A B t f s b) = (term547 A B t f s b).
Proof. exact (MK_COMB (@lem3479325 A B) (@lem3479324 A B t f s b)). Qed.
Lemma lem3479327 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (b : B) : (term506 A B t f s b) = (term547 A B t f s b).
Proof. exact (TRANS (@lem3479303 A B t f s b) (@lem3479326 A B t f s b)). Qed.
Lemma lem3479328 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : (term508 A B f s b) = (term548 A B f s b).
Proof. exact (fun_ext (fun t : type1413 A B => @lem3479327 A B t f s b)). Qed.
Lemma lem3479329 {A B : Type'} : (@ex (A -> B -> Prop)) = (@ex (A -> B -> Prop)).
Proof. exact (eq_refl (@ex (A -> B -> Prop))). Qed.
Lemma lem3479330 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : (term509 A B f s b) = (term549 A B f s b).
Proof. exact (MK_COMB (@lem3479329 A B) (@lem3479328 A B f s b)). Qed.
Lemma lem3479331 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : (term490 A B f s b) = (term549 A B f s b).
Proof. exact (TRANS (@lem3479276 A B f s b) (@lem3479330 A B f s b)). Qed.
Lemma lem3479333 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : (term349 A B f s b) = (term549 A B f s b).
Proof. exact (TRANS (@lem3479250 A B f s b) (@lem3479331 A B f s b)). Qed.
Lemma lem3479334 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : (term244 A B f s b) = (term549 A B f s b).
Proof. exact (TRANS (@lem3478659 A B f s b) (@lem3479333 A B f s b)). Qed.
Lemma lem3479335 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) (h1 : term244 A B f s b) : term549 A B f s b.
Proof. exact (EQ_MP (@lem3479334 A B f s b) (@lem3478523 A B f s b h1)). Qed.
Lemma lem3479336 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (h1 : term547 A B t f s b) : term547 A B t f s b.
Proof. exact (h1). Qed.
Lemma lem3479337 {A B : Type'} (t : type1413 A B) (x : type473 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (h1 : term545 A B t x f s b) : term545 A B t x f s b.
Proof. exact (h1). Qed.
Lemma lem3479338 {A B : Type'} (t : type1413 A B) (x : type473 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (g : type1413 A B) (h1 : term542 A B t x f s b g) : term542 A B t x f s b g.
Proof. exact (h1). Qed.
Lemma lem3479345 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3479346 {A B : Type'} (f : type1413 A B) (x : A) : (f x) = (@I (A -> B -> Prop) f x).
Proof. exact (@lem3479345 A (B -> Prop) f x). Qed.
Lemma lem3479348 {A B : Type'} (g : type1413 A B) (x : A) : (g x) = (@I (A -> B -> Prop) g x).
Proof. exact (@lem3479346 A B g x). Qed.
Lemma lem3479349 {B : Type'} (b : B) : (@IN B b) = (@IN B b).
Proof. exact (eq_refl (@IN B b)). Qed.
Lemma lem3479350 {A B : Type'} (b : B) (g : type1413 A B) (x : A) : (term269 A B b g x) = (term550 A B b g x).
Proof. exact (MK_COMB (@lem3479349 B b) (@lem3479348 A B g x)). Qed.
Lemma lem3479352 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3479353 {B : Type'} (f : type1364 B) (x : B) : (f x) = (@I (B -> (B -> Prop) -> Prop) f x).
Proof. exact (@lem3479352 B (type686 B) f x). Qed.
Lemma lem3479354 {B : Type'} (b : B) : (@IN B b) = (@I (B -> (B -> Prop) -> Prop) (@IN B) b).
Proof. exact (@lem3479353 B (@IN B) b). Qed.
Lemma lem3479355 {A B : Type'} (g : type1413 A B) (x : A) : (@I (A -> B -> Prop) g x) = (@I (A -> B -> Prop) g x).
Proof. exact (eq_refl (@I (A -> B -> Prop) g x)). Qed.
Lemma lem3479356 {A B : Type'} (b : B) (g : type1413 A B) (x : A) : (term550 A B b g x) = (term551 A B b g x).
Proof. exact (MK_COMB (@lem3479354 B b) (@lem3479355 A B g x)). Qed.
Lemma lem3479358 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3479359 {B : Type'} (f : type686 B) (x : B -> Prop) : (f x) = (@I ((B -> Prop) -> Prop) f x).
Proof. exact (@lem3479358 (B -> Prop) Prop f x). Qed.
Lemma lem3479360 {A B : Type'} (b : B) (g : type1413 A B) (x : A) : (term551 A B b g x) = (term552 A B b g x).
Proof. exact (@lem3479359 B (@I (B -> (B -> Prop) -> Prop) (@IN B) b) (@I (A -> B -> Prop) g x)). Qed.
Lemma lem3479361 {A B : Type'} (b : B) (g : type1413 A B) (x : A) : (term550 A B b g x) = (term552 A B b g x).
Proof. exact (TRANS (@lem3479356 A B b g x) (@lem3479360 A B b g x)). Qed.
Lemma lem3479362 {A B : Type'} (b : B) (g : type1413 A B) (x : A) : (term269 A B b g x) = (term552 A B b g x).
Proof. exact (TRANS (@lem3479350 A B b g x) (@lem3479361 A B b g x)). Qed.
Lemma lem3479363 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3479370 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3479371 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem3479370 A (type686 A) f x). Qed.
Lemma lem3479372 {A : Type'} (x : A) : (@IN A x) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x).
Proof. exact (@lem3479371 A (@IN A) x). Qed.
Lemma lem3479373 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem3479374 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x s).
Proof. exact (MK_COMB (@lem3479372 A x) (@lem3479373 A s)). Qed.
Lemma lem3479376 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3479377 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem3479376 (A -> Prop) Prop f x). Qed.
Lemma lem3479378 {A : Type'} (x : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x s) = (term553 A x s).
Proof. exact (@lem3479377 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x) s). Qed.
Lemma lem3479380 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (term553 A x s).
Proof. exact (TRANS (@lem3479374 A x s) (@lem3479378 A x s)). Qed.
Lemma lem3479381 {A : Type'} (x : A) (s : A -> Prop) : (term554 A x s) = (term555 A x s).
Proof. exact (MK_COMB (@lem3479363) (@lem3479380 A x s)). Qed.
Lemma lem3479382 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3479383 {A : Type'} (x : A) (s : A -> Prop) : (term556 A x s) = (term557 A x s).
Proof. exact (MK_COMB (@lem3479382) (@lem3479381 A x s)). Qed.
Lemma lem3479384 {A B : Type'} (s : A -> Prop) (b : B) (g : type1413 A B) (x : A) : (term312 A B s b g x) = (term558 A B s b g x).
Proof. exact (MK_COMB (@lem3479383 A x s) (@lem3479362 A B b g x)). Qed.
Lemma lem3479385 {A B : Type'} (s : A -> Prop) (b : B) (g : type1413 A B) : (term320 A B s b g) = (term559 A B s b g).
Proof. exact (fun_ext (fun x : A => @lem3479384 A B s b g x)). Qed.
Lemma lem3479386 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3479387 {A B : Type'} (s : A -> Prop) (b : B) (g : type1413 A B) : (term321 A B s b g) = (term560 A B s b g).
Proof. exact (MK_COMB (@lem3479386 A) (@lem3479385 A B s b g)). Qed.
Lemma lem3479388 {B : Type'} : (@IN (B -> Prop)) = (@IN (B -> Prop)).
Proof. exact (eq_refl (@IN (B -> Prop))). Qed.
Lemma lem3479393 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3479394 {A B : Type'} (f : type1413 A B) (x : A) : (f x) = (@I (A -> B -> Prop) f x).
Proof. exact (@lem3479393 A (B -> Prop) f x). Qed.
Lemma lem3479396 {A B : Type'} (g : type1413 A B) (x : A) : (g x) = (@I (A -> B -> Prop) g x).
Proof. exact (@lem3479394 A B g x). Qed.
Lemma lem3479401 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3479403 {A B : Type'} (f : type1374 A B) (x : A) : (f x) = (@I (A -> (B -> Prop) -> Prop) f x).
Proof. exact (@lem3479401 A (type686 B) f x). Qed.
Lemma lem3479404 {A B : Type'} (g : type1413 A B) (x : A) : (term561 A B g x) = (term562 A B g x).
Proof. exact (MK_COMB (@lem3479388 B) (@lem3479396 A B g x)). Qed.
Lemma lem3479405 {A B : Type'} (g : type1413 A B) (f : type1374 A B) (x : A) : (term268 A B g f x) = (term563 A B g f x).
Proof. exact (MK_COMB (@lem3479404 A B g x) (@lem3479403 A B f x)). Qed.
Lemma lem3479407 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3479408 {B : Type'} (f : type599 B) (x : B -> Prop) : (f x) = (@I ((B -> Prop) -> ((B -> Prop) -> Prop) -> Prop) f x).
Proof. exact (@lem3479407 (B -> Prop) (type180 B) f x). Qed.
Lemma lem3479409 {A B : Type'} (g : type1413 A B) (x : A) : (term562 A B g x) = (term564 A B g x).
Proof. exact (@lem3479408 B (@IN (B -> Prop)) (@I (A -> B -> Prop) g x)). Qed.
Lemma lem3479410 {A B : Type'} (f : type1374 A B) (x : A) : (@I (A -> (B -> Prop) -> Prop) f x) = (@I (A -> (B -> Prop) -> Prop) f x).
Proof. exact (eq_refl (@I (A -> (B -> Prop) -> Prop) f x)). Qed.
Lemma lem3479411 {A B : Type'} (g : type1413 A B) (f : type1374 A B) (x : A) : (term563 A B g f x) = (term565 A B g f x).
Proof. exact (MK_COMB (@lem3479409 A B g x) (@lem3479410 A B f x)). Qed.
Lemma lem3479413 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3479414 {B : Type'} (f : type180 B) (x : type686 B) : (f x) = (@I (((B -> Prop) -> Prop) -> Prop) f x).
Proof. exact (@lem3479413 (type686 B) Prop f x). Qed.
Lemma lem3479415 {A B : Type'} (g : type1413 A B) (f : type1374 A B) (x : A) : (term565 A B g f x) = (term566 A B g f x).
Proof. exact (@lem3479414 B (term564 A B g x) (@I (A -> (B -> Prop) -> Prop) f x)). Qed.
Lemma lem3479416 {A B : Type'} (g : type1413 A B) (f : type1374 A B) (x : A) : (term563 A B g f x) = (term566 A B g f x).
Proof. exact (TRANS (@lem3479411 A B g f x) (@lem3479415 A B g f x)). Qed.
Lemma lem3479417 {A B : Type'} (g : type1413 A B) (f : type1374 A B) (x : A) : (term268 A B g f x) = (term566 A B g f x).
Proof. exact (TRANS (@lem3479405 A B g f x) (@lem3479416 A B g f x)). Qed.
Lemma lem3479418 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3479425 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3479426 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem3479425 A (type686 A) f x). Qed.
Lemma lem3479427 {A : Type'} (x : A) : (@IN A x) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x).
Proof. exact (@lem3479426 A (@IN A) x). Qed.
Lemma lem3479428 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem3479429 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x s).
Proof. exact (MK_COMB (@lem3479427 A x) (@lem3479428 A s)). Qed.
Lemma lem3479431 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3479432 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem3479431 (A -> Prop) Prop f x). Qed.
Lemma lem3479433 {A : Type'} (x : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x s) = (term553 A x s).
Proof. exact (@lem3479432 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x) s). Qed.
Lemma lem3479435 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (term553 A x s).
Proof. exact (TRANS (@lem3479429 A x s) (@lem3479433 A x s)). Qed.
Lemma lem3479436 {A : Type'} (x : A) (s : A -> Prop) : (term554 A x s) = (term555 A x s).
Proof. exact (MK_COMB (@lem3479418) (@lem3479435 A x s)). Qed.
Lemma lem3479437 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3479438 {A : Type'} (x : A) (s : A -> Prop) : (term556 A x s) = (term557 A x s).
Proof. exact (MK_COMB (@lem3479437) (@lem3479436 A x s)). Qed.
Lemma lem3479439 {A B : Type'} (s : A -> Prop) (g : type1413 A B) (f : type1374 A B) (x : A) : (term300 A B s g f x) = (term567 A B s g f x).
Proof. exact (MK_COMB (@lem3479438 A x s) (@lem3479417 A B g f x)). Qed.
Lemma lem3479440 {A B : Type'} (s : A -> Prop) (g : type1413 A B) (f : type1374 A B) : (term308 A B s g f) = (term568 A B s g f).
Proof. exact (fun_ext (fun x : A => @lem3479439 A B s g f x)). Qed.
Lemma lem3479441 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3479442 {A B : Type'} (s : A -> Prop) (g : type1413 A B) (f : type1374 A B) : (term309 A B s g f) = (term569 A B s g f).
Proof. exact (MK_COMB (@lem3479441 A) (@lem3479440 A B s g f)). Qed.
Lemma lem3479443 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3479444 {A B : Type'} (s : A -> Prop) (g : type1413 A B) (f : type1374 A B) : (term327 A B s g f) = (term570 A B s g f).
Proof. exact (MK_COMB (@lem3479443) (@lem3479442 A B s g f)). Qed.
Lemma lem3479445 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) (g : type1413 A B) : (term328 A B f s b g) = (term571 A B f s b g).
Proof. exact (MK_COMB (@lem3479444 A B s g f) (@lem3479387 A B s b g)). Qed.
Lemma lem3479446 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3479449 {A B : Type'} (t : type1413 A B) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem3479454 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3479455 {A B : Type'} (f : type473 A B) (x : type1413 A B) : (f x) = (@I ((A -> B -> Prop) -> A) f x).
Proof. exact (@lem3479454 (type1413 A B) A f x). Qed.
Lemma lem3479457 {A B : Type'} (x : type473 A B) (t : type1413 A B) : (x t) = (@I ((A -> B -> Prop) -> A) x t).
Proof. exact (@lem3479455 A B x t). Qed.
Lemma lem3479458 {A B : Type'} (x : type473 A B) (t : type1413 A B) : (term572 A B x t) = (term573 A B x t).
Proof. exact (MK_COMB (@lem3479449 A B t) (@lem3479457 A B x t)). Qed.
Lemma lem3479460 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3479461 {A B : Type'} (f : type1413 A B) (x : A) : (f x) = (@I (A -> B -> Prop) f x).
Proof. exact (@lem3479460 A (B -> Prop) f x). Qed.
Lemma lem3479462 {A B : Type'} (x : type473 A B) (t : type1413 A B) : (term573 A B x t) = (term574 A B x t).
Proof. exact (@lem3479461 A B t (@I ((A -> B -> Prop) -> A) x t)). Qed.
Lemma lem3479463 {A B : Type'} (x : type473 A B) (t : type1413 A B) : (term572 A B x t) = (term574 A B x t).
Proof. exact (TRANS (@lem3479458 A B x t) (@lem3479462 A B x t)). Qed.
Lemma lem3479464 {B : Type'} (b : B) : (@IN B b) = (@IN B b).
Proof. exact (eq_refl (@IN B b)). Qed.
Lemma lem3479465 {A B : Type'} (b : B) (x : type473 A B) (t : type1413 A B) : (term575 A B b x t) = (term576 A B b x t).
Proof. exact (MK_COMB (@lem3479464 B b) (@lem3479463 A B x t)). Qed.
Lemma lem3479467 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3479468 {B : Type'} (f : type1364 B) (x : B) : (f x) = (@I (B -> (B -> Prop) -> Prop) f x).
Proof. exact (@lem3479467 B (type686 B) f x). Qed.
Lemma lem3479469 {B : Type'} (b : B) : (@IN B b) = (@I (B -> (B -> Prop) -> Prop) (@IN B) b).
Proof. exact (@lem3479468 B (@IN B) b). Qed.
Lemma lem3479470 {A B : Type'} (x : type473 A B) (t : type1413 A B) : (term574 A B x t) = (term574 A B x t).
Proof. exact (eq_refl (term574 A B x t)). Qed.
Lemma lem3479471 {A B : Type'} (b : B) (x : type473 A B) (t : type1413 A B) : (term576 A B b x t) = (term577 A B b x t).
Proof. exact (MK_COMB (@lem3479469 B b) (@lem3479470 A B x t)). Qed.
Lemma lem3479473 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3479474 {B : Type'} (f : type686 B) (x : B -> Prop) : (f x) = (@I ((B -> Prop) -> Prop) f x).
Proof. exact (@lem3479473 (B -> Prop) Prop f x). Qed.
Lemma lem3479475 {A B : Type'} (b : B) (x : type473 A B) (t : type1413 A B) : (term577 A B b x t) = (term578 A B b x t).
Proof. exact (@lem3479474 B (@I (B -> (B -> Prop) -> Prop) (@IN B) b) (term574 A B x t)). Qed.
Lemma lem3479476 {A B : Type'} (b : B) (x : type473 A B) (t : type1413 A B) : (term576 A B b x t) = (term578 A B b x t).
Proof. exact (TRANS (@lem3479471 A B b x t) (@lem3479475 A B b x t)). Qed.
Lemma lem3479477 {A B : Type'} (b : B) (x : type473 A B) (t : type1413 A B) : (term575 A B b x t) = (term578 A B b x t).
Proof. exact (TRANS (@lem3479465 A B b x t) (@lem3479476 A B b x t)). Qed.
Lemma lem3479478 {A B : Type'} (b : B) (x : type473 A B) (t : type1413 A B) : (term579 A B b x t) = (term580 A B b x t).
Proof. exact (MK_COMB (@lem3479446) (@lem3479477 A B b x t)). Qed.
Lemma lem3479479 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3479480 {B : Type'} : (@IN (B -> Prop)) = (@IN (B -> Prop)).
Proof. exact (eq_refl (@IN (B -> Prop))). Qed.
Lemma lem3479481 {A B : Type'} (t : type1413 A B) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem3479486 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3479487 {A B : Type'} (f : type473 A B) (x : type1413 A B) : (f x) = (@I ((A -> B -> Prop) -> A) f x).
Proof. exact (@lem3479486 (type1413 A B) A f x). Qed.
Lemma lem3479489 {A B : Type'} (x : type473 A B) (t : type1413 A B) : (x t) = (@I ((A -> B -> Prop) -> A) x t).
Proof. exact (@lem3479487 A B x t). Qed.
Lemma lem3479490 {A B : Type'} (x : type473 A B) (t : type1413 A B) : (term572 A B x t) = (term573 A B x t).
Proof. exact (MK_COMB (@lem3479481 A B t) (@lem3479489 A B x t)). Qed.
Lemma lem3479492 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3479493 {A B : Type'} (f : type1413 A B) (x : A) : (f x) = (@I (A -> B -> Prop) f x).
Proof. exact (@lem3479492 A (B -> Prop) f x). Qed.
Lemma lem3479494 {A B : Type'} (x : type473 A B) (t : type1413 A B) : (term573 A B x t) = (term574 A B x t).
Proof. exact (@lem3479493 A B t (@I ((A -> B -> Prop) -> A) x t)). Qed.
Lemma lem3479495 {A B : Type'} (x : type473 A B) (t : type1413 A B) : (term572 A B x t) = (term574 A B x t).
Proof. exact (TRANS (@lem3479490 A B x t) (@lem3479494 A B x t)). Qed.
Lemma lem3479496 {A B : Type'} (f : type1374 A B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem3479501 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3479502 {A B : Type'} (f : type473 A B) (x : type1413 A B) : (f x) = (@I ((A -> B -> Prop) -> A) f x).
Proof. exact (@lem3479501 (type1413 A B) A f x). Qed.
Lemma lem3479504 {A B : Type'} (x : type473 A B) (t : type1413 A B) : (x t) = (@I ((A -> B -> Prop) -> A) x t).
Proof. exact (@lem3479502 A B x t). Qed.
Lemma lem3479505 {A B : Type'} (f : type1374 A B) (x : type473 A B) (t : type1413 A B) : (term581 A B f x t) = (term582 A B f x t).
Proof. exact (MK_COMB (@lem3479496 A B f) (@lem3479504 A B x t)). Qed.
Lemma lem3479507 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3479508 {A B : Type'} (f : type1374 A B) (x : A) : (f x) = (@I (A -> (B -> Prop) -> Prop) f x).
Proof. exact (@lem3479507 A (type686 B) f x). Qed.
Lemma lem3479509 {A B : Type'} (f : type1374 A B) (x : type473 A B) (t : type1413 A B) : (term582 A B f x t) = (term583 A B f x t).
Proof. exact (@lem3479508 A B f (@I ((A -> B -> Prop) -> A) x t)). Qed.
Lemma lem3479510 {A B : Type'} (f : type1374 A B) (x : type473 A B) (t : type1413 A B) : (term581 A B f x t) = (term583 A B f x t).
Proof. exact (TRANS (@lem3479505 A B f x t) (@lem3479509 A B f x t)). Qed.
Lemma lem3479511 {A B : Type'} (x : type473 A B) (t : type1413 A B) : (term584 A B x t) = (term585 A B x t).
Proof. exact (MK_COMB (@lem3479480 B) (@lem3479495 A B x t)). Qed.
Lemma lem3479512 {A B : Type'} (f : type1374 A B) (x : type473 A B) (t : type1413 A B) : (term586 A B f x t) = (term587 A B f x t).
Proof. exact (MK_COMB (@lem3479511 A B x t) (@lem3479510 A B f x t)). Qed.
Lemma lem3479514 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3479515 {B : Type'} (f : type599 B) (x : B -> Prop) : (f x) = (@I ((B -> Prop) -> ((B -> Prop) -> Prop) -> Prop) f x).
Proof. exact (@lem3479514 (B -> Prop) (type180 B) f x). Qed.
Lemma lem3479516 {A B : Type'} (x : type473 A B) (t : type1413 A B) : (term585 A B x t) = (term588 A B x t).
Proof. exact (@lem3479515 B (@IN (B -> Prop)) (term574 A B x t)). Qed.
Lemma lem3479517 {A B : Type'} (f : type1374 A B) (x : type473 A B) (t : type1413 A B) : (term583 A B f x t) = (term583 A B f x t).
Proof. exact (eq_refl (term583 A B f x t)). Qed.
Lemma lem3479518 {A B : Type'} (f : type1374 A B) (x : type473 A B) (t : type1413 A B) : (term587 A B f x t) = (term589 A B f x t).
Proof. exact (MK_COMB (@lem3479516 A B x t) (@lem3479517 A B f x t)). Qed.
Lemma lem3479520 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3479521 {B : Type'} (f : type180 B) (x : type686 B) : (f x) = (@I (((B -> Prop) -> Prop) -> Prop) f x).
Proof. exact (@lem3479520 (type686 B) Prop f x). Qed.
Lemma lem3479522 {A B : Type'} (f : type1374 A B) (x : type473 A B) (t : type1413 A B) : (term589 A B f x t) = (term590 A B f x t).
Proof. exact (@lem3479521 B (term588 A B x t) (term583 A B f x t)). Qed.
Lemma lem3479523 {A B : Type'} (f : type1374 A B) (x : type473 A B) (t : type1413 A B) : (term587 A B f x t) = (term590 A B f x t).
Proof. exact (TRANS (@lem3479518 A B f x t) (@lem3479522 A B f x t)). Qed.
Lemma lem3479524 {A B : Type'} (f : type1374 A B) (x : type473 A B) (t : type1413 A B) : (term586 A B f x t) = (term590 A B f x t).
Proof. exact (TRANS (@lem3479512 A B f x t) (@lem3479523 A B f x t)). Qed.
Lemma lem3479525 {A B : Type'} (f : type1374 A B) (x : type473 A B) (t : type1413 A B) : (term591 A B f x t) = (term592 A B f x t).
Proof. exact (MK_COMB (@lem3479479) (@lem3479524 A B f x t)). Qed.
Lemma lem3479526 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3479527 {A B : Type'} (f : type1374 A B) (x : type473 A B) (t : type1413 A B) : (term593 A B f x t) = (term594 A B f x t).
Proof. exact (MK_COMB (@lem3479526) (@lem3479525 A B f x t)). Qed.
Lemma lem3479528 {A B : Type'} (f : type1374 A B) (b : B) (x : type473 A B) (t : type1413 A B) : (term595 A B f b x t) = (term596 A B f b x t).
Proof. exact (MK_COMB (@lem3479527 A B f x t) (@lem3479478 A B b x t)). Qed.
Lemma lem3479529 {A : Type'} : (@IN A) = (@IN A).
Proof. exact (eq_refl (@IN A)). Qed.
Lemma lem3479534 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3479535 {A B : Type'} (f : type473 A B) (x : type1413 A B) : (f x) = (@I ((A -> B -> Prop) -> A) f x).
Proof. exact (@lem3479534 (type1413 A B) A f x). Qed.
Lemma lem3479537 {A B : Type'} (x : type473 A B) (t : type1413 A B) : (x t) = (@I ((A -> B -> Prop) -> A) x t).
Proof. exact (@lem3479535 A B x t). Qed.
Lemma lem3479538 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem3479539 {A B : Type'} (x : type473 A B) (t : type1413 A B) : (term597 A B x t) = (term598 A B x t).
Proof. exact (MK_COMB (@lem3479529 A) (@lem3479537 A B x t)). Qed.
Lemma lem3479540 {A B : Type'} (x : type473 A B) (t : type1413 A B) (s : A -> Prop) : (term599 A B x t s) = (term600 A B x t s).
Proof. exact (MK_COMB (@lem3479539 A B x t) (@lem3479538 A s)). Qed.
Lemma lem3479542 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3479543 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem3479542 A (type686 A) f x). Qed.
Lemma lem3479544 {A B : Type'} (x : type473 A B) (t : type1413 A B) : (term598 A B x t) = (term601 A B x t).
Proof. exact (@lem3479543 A (@IN A) (@I ((A -> B -> Prop) -> A) x t)). Qed.
Lemma lem3479545 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem3479546 {A B : Type'} (x : type473 A B) (t : type1413 A B) (s : A -> Prop) : (term600 A B x t s) = (term602 A B x t s).
Proof. exact (MK_COMB (@lem3479544 A B x t) (@lem3479545 A s)). Qed.
Lemma lem3479548 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3479549 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem3479548 (A -> Prop) Prop f x). Qed.
Lemma lem3479550 {A B : Type'} (x : type473 A B) (t : type1413 A B) (s : A -> Prop) : (term602 A B x t s) = (term603 A B x t s).
Proof. exact (@lem3479549 A (term601 A B x t) s). Qed.
Lemma lem3479551 {A B : Type'} (x : type473 A B) (t : type1413 A B) (s : A -> Prop) : (term600 A B x t s) = (term603 A B x t s).
Proof. exact (TRANS (@lem3479546 A B x t s) (@lem3479550 A B x t s)). Qed.
Lemma lem3479552 {A B : Type'} (x : type473 A B) (t : type1413 A B) (s : A -> Prop) : (term599 A B x t s) = (term603 A B x t s).
Proof. exact (TRANS (@lem3479540 A B x t s) (@lem3479551 A B x t s)). Qed.
Lemma lem3479553 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3479554 {A B : Type'} (x : type473 A B) (t : type1413 A B) (s : A -> Prop) : (term604 A B x t s) = (term605 A B x t s).
Proof. exact (MK_COMB (@lem3479553) (@lem3479552 A B x t s)). Qed.
Lemma lem3479555 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) (x : type473 A B) (t : type1413 A B) : (term447 A B s f b x t) = (term606 A B s f b x t).
Proof. exact (MK_COMB (@lem3479554 A B x t s) (@lem3479528 A B f b x t)). Qed.
Lemma lem3479556 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) (x : type473 A B) : (term449 A B s f b x) = (term607 A B s f b x).
Proof. exact (fun_ext (fun t : type1413 A B => @lem3479555 A B s f b x t)). Qed.
Lemma lem3479557 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem3479558 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) (x : type473 A B) : (term451 A B s f b x) = (term608 A B s f b x).
Proof. exact (MK_COMB (@lem3479557 A B) (@lem3479556 A B s f b x)). Qed.
Lemma lem3479559 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3479560 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) (x : type473 A B) : (term468 A B s f b x) = (term609 A B s f b x).
Proof. exact (MK_COMB (@lem3479559) (@lem3479558 A B s f b x)). Qed.
Lemma lem3479561 {A B : Type'} (x : type473 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (g : type1413 A B) : (term484 A B x f s b g) = (term610 A B x f s b g).
Proof. exact (MK_COMB (@lem3479560 A B s f b x) (@lem3479445 A B f s b g)). Qed.
Lemma lem3479562 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3479565 {A B : Type'} (g : type1413 A B) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem3479570 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3479571 {A B : Type'} (f : type473 A B) (x : type1413 A B) : (f x) = (@I ((A -> B -> Prop) -> A) f x).
Proof. exact (@lem3479570 (type1413 A B) A f x). Qed.
Lemma lem3479573 {A B : Type'} (x : type473 A B) (g : type1413 A B) : (x g) = (@I ((A -> B -> Prop) -> A) x g).
Proof. exact (@lem3479571 A B x g). Qed.
Lemma lem3479574 {A B : Type'} (x : type473 A B) (g : type1413 A B) : (term572 A B x g) = (term573 A B x g).
Proof. exact (MK_COMB (@lem3479565 A B g) (@lem3479573 A B x g)). Qed.
Lemma lem3479576 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3479577 {A B : Type'} (f : type1413 A B) (x : A) : (f x) = (@I (A -> B -> Prop) f x).
Proof. exact (@lem3479576 A (B -> Prop) f x). Qed.
Lemma lem3479578 {A B : Type'} (x : type473 A B) (g : type1413 A B) : (term573 A B x g) = (term574 A B x g).
Proof. exact (@lem3479577 A B g (@I ((A -> B -> Prop) -> A) x g)). Qed.
Lemma lem3479579 {A B : Type'} (x : type473 A B) (g : type1413 A B) : (term572 A B x g) = (term574 A B x g).
Proof. exact (TRANS (@lem3479574 A B x g) (@lem3479578 A B x g)). Qed.
Lemma lem3479580 {B : Type'} (b : B) : (@IN B b) = (@IN B b).
Proof. exact (eq_refl (@IN B b)). Qed.
Lemma lem3479581 {A B : Type'} (b : B) (x : type473 A B) (g : type1413 A B) : (term575 A B b x g) = (term576 A B b x g).
Proof. exact (MK_COMB (@lem3479580 B b) (@lem3479579 A B x g)). Qed.
Lemma lem3479583 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3479584 {B : Type'} (f : type1364 B) (x : B) : (f x) = (@I (B -> (B -> Prop) -> Prop) f x).
Proof. exact (@lem3479583 B (type686 B) f x). Qed.
Lemma lem3479585 {B : Type'} (b : B) : (@IN B b) = (@I (B -> (B -> Prop) -> Prop) (@IN B) b).
Proof. exact (@lem3479584 B (@IN B) b). Qed.
Lemma lem3479586 {A B : Type'} (x : type473 A B) (g : type1413 A B) : (term574 A B x g) = (term574 A B x g).
Proof. exact (eq_refl (term574 A B x g)). Qed.
Lemma lem3479587 {A B : Type'} (b : B) (x : type473 A B) (g : type1413 A B) : (term576 A B b x g) = (term577 A B b x g).
Proof. exact (MK_COMB (@lem3479585 B b) (@lem3479586 A B x g)). Qed.
Lemma lem3479589 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3479590 {B : Type'} (f : type686 B) (x : B -> Prop) : (f x) = (@I ((B -> Prop) -> Prop) f x).
Proof. exact (@lem3479589 (B -> Prop) Prop f x). Qed.
Lemma lem3479591 {A B : Type'} (b : B) (x : type473 A B) (g : type1413 A B) : (term577 A B b x g) = (term578 A B b x g).
Proof. exact (@lem3479590 B (@I (B -> (B -> Prop) -> Prop) (@IN B) b) (term574 A B x g)). Qed.
Lemma lem3479592 {A B : Type'} (b : B) (x : type473 A B) (g : type1413 A B) : (term576 A B b x g) = (term578 A B b x g).
Proof. exact (TRANS (@lem3479587 A B b x g) (@lem3479591 A B b x g)). Qed.
Lemma lem3479593 {A B : Type'} (b : B) (x : type473 A B) (g : type1413 A B) : (term575 A B b x g) = (term578 A B b x g).
Proof. exact (TRANS (@lem3479581 A B b x g) (@lem3479592 A B b x g)). Qed.
Lemma lem3479594 {A B : Type'} (b : B) (x : type473 A B) (g : type1413 A B) : (term579 A B b x g) = (term580 A B b x g).
Proof. exact (MK_COMB (@lem3479562) (@lem3479593 A B b x g)). Qed.
Lemma lem3479595 {A : Type'} : (@IN A) = (@IN A).
Proof. exact (eq_refl (@IN A)). Qed.
Lemma lem3479600 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3479601 {A B : Type'} (f : type473 A B) (x : type1413 A B) : (f x) = (@I ((A -> B -> Prop) -> A) f x).
Proof. exact (@lem3479600 (type1413 A B) A f x). Qed.
Lemma lem3479603 {A B : Type'} (x : type473 A B) (g : type1413 A B) : (x g) = (@I ((A -> B -> Prop) -> A) x g).
Proof. exact (@lem3479601 A B x g). Qed.
Lemma lem3479604 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem3479605 {A B : Type'} (x : type473 A B) (g : type1413 A B) : (term597 A B x g) = (term598 A B x g).
Proof. exact (MK_COMB (@lem3479595 A) (@lem3479603 A B x g)). Qed.
Lemma lem3479606 {A B : Type'} (x : type473 A B) (g : type1413 A B) (s : A -> Prop) : (term599 A B x g s) = (term600 A B x g s).
Proof. exact (MK_COMB (@lem3479605 A B x g) (@lem3479604 A s)). Qed.
Lemma lem3479608 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3479609 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem3479608 A (type686 A) f x). Qed.
Lemma lem3479610 {A B : Type'} (x : type473 A B) (g : type1413 A B) : (term598 A B x g) = (term601 A B x g).
Proof. exact (@lem3479609 A (@IN A) (@I ((A -> B -> Prop) -> A) x g)). Qed.
Lemma lem3479611 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem3479612 {A B : Type'} (x : type473 A B) (g : type1413 A B) (s : A -> Prop) : (term600 A B x g s) = (term602 A B x g s).
Proof. exact (MK_COMB (@lem3479610 A B x g) (@lem3479611 A s)). Qed.
Lemma lem3479614 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3479615 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem3479614 (A -> Prop) Prop f x). Qed.
Lemma lem3479616 {A B : Type'} (x : type473 A B) (g : type1413 A B) (s : A -> Prop) : (term602 A B x g s) = (term603 A B x g s).
Proof. exact (@lem3479615 A (term601 A B x g) s). Qed.
Lemma lem3479617 {A B : Type'} (x : type473 A B) (g : type1413 A B) (s : A -> Prop) : (term600 A B x g s) = (term603 A B x g s).
Proof. exact (TRANS (@lem3479612 A B x g s) (@lem3479616 A B x g s)). Qed.
Lemma lem3479618 {A B : Type'} (x : type473 A B) (g : type1413 A B) (s : A -> Prop) : (term599 A B x g s) = (term603 A B x g s).
Proof. exact (TRANS (@lem3479606 A B x g s) (@lem3479617 A B x g s)). Qed.
Lemma lem3479619 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3479620 {A B : Type'} (x : type473 A B) (g : type1413 A B) (s : A -> Prop) : (term604 A B x g s) = (term605 A B x g s).
Proof. exact (MK_COMB (@lem3479619) (@lem3479618 A B x g s)). Qed.
Lemma lem3479621 {A B : Type'} (s : A -> Prop) (b : B) (x : type473 A B) (g : type1413 A B) : (term611 A B s b x g) = (term612 A B s b x g).
Proof. exact (MK_COMB (@lem3479620 A B x g s) (@lem3479594 A B b x g)). Qed.
Lemma lem3479622 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3479623 {B : Type'} : (@IN (B -> Prop)) = (@IN (B -> Prop)).
Proof. exact (eq_refl (@IN (B -> Prop))). Qed.
Lemma lem3479624 {A B : Type'} (g : type1413 A B) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem3479629 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3479630 {A B : Type'} (f : type473 A B) (x : type1413 A B) : (f x) = (@I ((A -> B -> Prop) -> A) f x).
Proof. exact (@lem3479629 (type1413 A B) A f x). Qed.
Lemma lem3479632 {A B : Type'} (x : type473 A B) (g : type1413 A B) : (x g) = (@I ((A -> B -> Prop) -> A) x g).
Proof. exact (@lem3479630 A B x g). Qed.
Lemma lem3479633 {A B : Type'} (x : type473 A B) (g : type1413 A B) : (term572 A B x g) = (term573 A B x g).
Proof. exact (MK_COMB (@lem3479624 A B g) (@lem3479632 A B x g)). Qed.
Lemma lem3479635 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3479636 {A B : Type'} (f : type1413 A B) (x : A) : (f x) = (@I (A -> B -> Prop) f x).
Proof. exact (@lem3479635 A (B -> Prop) f x). Qed.
Lemma lem3479637 {A B : Type'} (x : type473 A B) (g : type1413 A B) : (term573 A B x g) = (term574 A B x g).
Proof. exact (@lem3479636 A B g (@I ((A -> B -> Prop) -> A) x g)). Qed.
Lemma lem3479638 {A B : Type'} (x : type473 A B) (g : type1413 A B) : (term572 A B x g) = (term574 A B x g).
Proof. exact (TRANS (@lem3479633 A B x g) (@lem3479637 A B x g)). Qed.
Lemma lem3479639 {A B : Type'} (f : type1374 A B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem3479644 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3479645 {A B : Type'} (f : type473 A B) (x : type1413 A B) : (f x) = (@I ((A -> B -> Prop) -> A) f x).
Proof. exact (@lem3479644 (type1413 A B) A f x). Qed.
Lemma lem3479647 {A B : Type'} (x : type473 A B) (g : type1413 A B) : (x g) = (@I ((A -> B -> Prop) -> A) x g).
Proof. exact (@lem3479645 A B x g). Qed.
Lemma lem3479648 {A B : Type'} (f : type1374 A B) (x : type473 A B) (g : type1413 A B) : (term581 A B f x g) = (term582 A B f x g).
Proof. exact (MK_COMB (@lem3479639 A B f) (@lem3479647 A B x g)). Qed.
Lemma lem3479650 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3479651 {A B : Type'} (f : type1374 A B) (x : A) : (f x) = (@I (A -> (B -> Prop) -> Prop) f x).
Proof. exact (@lem3479650 A (type686 B) f x). Qed.
Lemma lem3479652 {A B : Type'} (f : type1374 A B) (x : type473 A B) (g : type1413 A B) : (term582 A B f x g) = (term583 A B f x g).
Proof. exact (@lem3479651 A B f (@I ((A -> B -> Prop) -> A) x g)). Qed.
Lemma lem3479653 {A B : Type'} (f : type1374 A B) (x : type473 A B) (g : type1413 A B) : (term581 A B f x g) = (term583 A B f x g).
Proof. exact (TRANS (@lem3479648 A B f x g) (@lem3479652 A B f x g)). Qed.
Lemma lem3479654 {A B : Type'} (x : type473 A B) (g : type1413 A B) : (term584 A B x g) = (term585 A B x g).
Proof. exact (MK_COMB (@lem3479623 B) (@lem3479638 A B x g)). Qed.
Lemma lem3479655 {A B : Type'} (f : type1374 A B) (x : type473 A B) (g : type1413 A B) : (term586 A B f x g) = (term587 A B f x g).
Proof. exact (MK_COMB (@lem3479654 A B x g) (@lem3479653 A B f x g)). Qed.
Lemma lem3479657 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3479658 {B : Type'} (f : type599 B) (x : B -> Prop) : (f x) = (@I ((B -> Prop) -> ((B -> Prop) -> Prop) -> Prop) f x).
Proof. exact (@lem3479657 (B -> Prop) (type180 B) f x). Qed.
Lemma lem3479659 {A B : Type'} (x : type473 A B) (g : type1413 A B) : (term585 A B x g) = (term588 A B x g).
Proof. exact (@lem3479658 B (@IN (B -> Prop)) (term574 A B x g)). Qed.
Lemma lem3479660 {A B : Type'} (f : type1374 A B) (x : type473 A B) (g : type1413 A B) : (term583 A B f x g) = (term583 A B f x g).
Proof. exact (eq_refl (term583 A B f x g)). Qed.
Lemma lem3479661 {A B : Type'} (f : type1374 A B) (x : type473 A B) (g : type1413 A B) : (term587 A B f x g) = (term589 A B f x g).
Proof. exact (MK_COMB (@lem3479659 A B x g) (@lem3479660 A B f x g)). Qed.
Lemma lem3479663 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3479664 {B : Type'} (f : type180 B) (x : type686 B) : (f x) = (@I (((B -> Prop) -> Prop) -> Prop) f x).
Proof. exact (@lem3479663 (type686 B) Prop f x). Qed.
Lemma lem3479665 {A B : Type'} (f : type1374 A B) (x : type473 A B) (g : type1413 A B) : (term589 A B f x g) = (term590 A B f x g).
Proof. exact (@lem3479664 B (term588 A B x g) (term583 A B f x g)). Qed.
Lemma lem3479666 {A B : Type'} (f : type1374 A B) (x : type473 A B) (g : type1413 A B) : (term587 A B f x g) = (term590 A B f x g).
Proof. exact (TRANS (@lem3479661 A B f x g) (@lem3479665 A B f x g)). Qed.
Lemma lem3479667 {A B : Type'} (f : type1374 A B) (x : type473 A B) (g : type1413 A B) : (term586 A B f x g) = (term590 A B f x g).
Proof. exact (TRANS (@lem3479655 A B f x g) (@lem3479666 A B f x g)). Qed.
Lemma lem3479668 {A B : Type'} (f : type1374 A B) (x : type473 A B) (g : type1413 A B) : (term591 A B f x g) = (term592 A B f x g).
Proof. exact (MK_COMB (@lem3479622) (@lem3479667 A B f x g)). Qed.
Lemma lem3479669 {A : Type'} : (@IN A) = (@IN A).
Proof. exact (eq_refl (@IN A)). Qed.
Lemma lem3479674 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3479675 {A B : Type'} (f : type473 A B) (x : type1413 A B) : (f x) = (@I ((A -> B -> Prop) -> A) f x).
Proof. exact (@lem3479674 (type1413 A B) A f x). Qed.
Lemma lem3479677 {A B : Type'} (x : type473 A B) (g : type1413 A B) : (x g) = (@I ((A -> B -> Prop) -> A) x g).
Proof. exact (@lem3479675 A B x g). Qed.
Lemma lem3479678 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem3479679 {A B : Type'} (x : type473 A B) (g : type1413 A B) : (term597 A B x g) = (term598 A B x g).
Proof. exact (MK_COMB (@lem3479669 A) (@lem3479677 A B x g)). Qed.
Lemma lem3479680 {A B : Type'} (x : type473 A B) (g : type1413 A B) (s : A -> Prop) : (term599 A B x g s) = (term600 A B x g s).
Proof. exact (MK_COMB (@lem3479679 A B x g) (@lem3479678 A s)). Qed.
Lemma lem3479682 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3479683 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem3479682 A (type686 A) f x). Qed.
Lemma lem3479684 {A B : Type'} (x : type473 A B) (g : type1413 A B) : (term598 A B x g) = (term601 A B x g).
Proof. exact (@lem3479683 A (@IN A) (@I ((A -> B -> Prop) -> A) x g)). Qed.
Lemma lem3479685 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem3479686 {A B : Type'} (x : type473 A B) (g : type1413 A B) (s : A -> Prop) : (term600 A B x g s) = (term602 A B x g s).
Proof. exact (MK_COMB (@lem3479684 A B x g) (@lem3479685 A s)). Qed.
Lemma lem3479688 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3479689 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem3479688 (A -> Prop) Prop f x). Qed.
Lemma lem3479690 {A B : Type'} (x : type473 A B) (g : type1413 A B) (s : A -> Prop) : (term602 A B x g s) = (term603 A B x g s).
Proof. exact (@lem3479689 A (term601 A B x g) s). Qed.
Lemma lem3479691 {A B : Type'} (x : type473 A B) (g : type1413 A B) (s : A -> Prop) : (term600 A B x g s) = (term603 A B x g s).
Proof. exact (TRANS (@lem3479686 A B x g s) (@lem3479690 A B x g s)). Qed.
Lemma lem3479692 {A B : Type'} (x : type473 A B) (g : type1413 A B) (s : A -> Prop) : (term599 A B x g s) = (term603 A B x g s).
Proof. exact (TRANS (@lem3479680 A B x g s) (@lem3479691 A B x g s)). Qed.
Lemma lem3479693 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3479694 {A B : Type'} (x : type473 A B) (g : type1413 A B) (s : A -> Prop) : (term604 A B x g s) = (term605 A B x g s).
Proof. exact (MK_COMB (@lem3479693) (@lem3479692 A B x g s)). Qed.
Lemma lem3479695 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : type473 A B) (g : type1413 A B) : (term613 A B s f x g) = (term614 A B s f x g).
Proof. exact (MK_COMB (@lem3479694 A B x g s) (@lem3479668 A B f x g)). Qed.
Lemma lem3479696 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3479697 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : type473 A B) (g : type1413 A B) : (term615 A B s f x g) = (term616 A B s f x g).
Proof. exact (MK_COMB (@lem3479696) (@lem3479695 A B s f x g)). Qed.
Lemma lem3479698 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) (x : type473 A B) (g : type1413 A B) : (term387 A B f s b x g) = (term617 A B f s b x g).
Proof. exact (MK_COMB (@lem3479697 A B s f x g) (@lem3479621 A B s b x g)). Qed.
Lemma lem3479699 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) (x : type473 A B) : (term389 A B f s b x) = (term618 A B f s b x).
Proof. exact (fun_ext (fun g : type1413 A B => @lem3479698 A B f s b x g)). Qed.
Lemma lem3479700 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem3479701 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) (x : type473 A B) : (term391 A B f s b x) = (term619 A B f s b x).
Proof. exact (MK_COMB (@lem3479700 A B) (@lem3479699 A B f s b x)). Qed.
Lemma lem3479708 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3479709 {A B : Type'} (f : type1413 A B) (x : A) : (f x) = (@I (A -> B -> Prop) f x).
Proof. exact (@lem3479708 A (B -> Prop) f x). Qed.
Lemma lem3479711 {A B : Type'} (t : type1413 A B) (x : A) : (t x) = (@I (A -> B -> Prop) t x).
Proof. exact (@lem3479709 A B t x). Qed.
Lemma lem3479712 {B : Type'} (b : B) : (@IN B b) = (@IN B b).
Proof. exact (eq_refl (@IN B b)). Qed.
Lemma lem3479713 {A B : Type'} (b : B) (t : type1413 A B) (x : A) : (term269 A B b t x) = (term550 A B b t x).
Proof. exact (MK_COMB (@lem3479712 B b) (@lem3479711 A B t x)). Qed.
Lemma lem3479715 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3479716 {B : Type'} (f : type1364 B) (x : B) : (f x) = (@I (B -> (B -> Prop) -> Prop) f x).
Proof. exact (@lem3479715 B (type686 B) f x). Qed.
Lemma lem3479717 {B : Type'} (b : B) : (@IN B b) = (@I (B -> (B -> Prop) -> Prop) (@IN B) b).
Proof. exact (@lem3479716 B (@IN B) b). Qed.
Lemma lem3479718 {A B : Type'} (t : type1413 A B) (x : A) : (@I (A -> B -> Prop) t x) = (@I (A -> B -> Prop) t x).
Proof. exact (eq_refl (@I (A -> B -> Prop) t x)). Qed.
Lemma lem3479719 {A B : Type'} (b : B) (t : type1413 A B) (x : A) : (term550 A B b t x) = (term551 A B b t x).
Proof. exact (MK_COMB (@lem3479717 B b) (@lem3479718 A B t x)). Qed.
Lemma lem3479721 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3479722 {B : Type'} (f : type686 B) (x : B -> Prop) : (f x) = (@I ((B -> Prop) -> Prop) f x).
Proof. exact (@lem3479721 (B -> Prop) Prop f x). Qed.
Lemma lem3479723 {A B : Type'} (b : B) (t : type1413 A B) (x : A) : (term551 A B b t x) = (term552 A B b t x).
Proof. exact (@lem3479722 B (@I (B -> (B -> Prop) -> Prop) (@IN B) b) (@I (A -> B -> Prop) t x)). Qed.
Lemma lem3479724 {A B : Type'} (b : B) (t : type1413 A B) (x : A) : (term550 A B b t x) = (term552 A B b t x).
Proof. exact (TRANS (@lem3479719 A B b t x) (@lem3479723 A B b t x)). Qed.
Lemma lem3479725 {A B : Type'} (b : B) (t : type1413 A B) (x : A) : (term269 A B b t x) = (term552 A B b t x).
Proof. exact (TRANS (@lem3479713 A B b t x) (@lem3479724 A B b t x)). Qed.
Lemma lem3479726 {B : Type'} : (@IN (B -> Prop)) = (@IN (B -> Prop)).
Proof. exact (eq_refl (@IN (B -> Prop))). Qed.
Lemma lem3479731 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3479732 {A B : Type'} (f : type1413 A B) (x : A) : (f x) = (@I (A -> B -> Prop) f x).
Proof. exact (@lem3479731 A (B -> Prop) f x). Qed.
Lemma lem3479734 {A B : Type'} (t : type1413 A B) (x : A) : (t x) = (@I (A -> B -> Prop) t x).
Proof. exact (@lem3479732 A B t x). Qed.
Lemma lem3479739 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3479741 {A B : Type'} (f : type1374 A B) (x : A) : (f x) = (@I (A -> (B -> Prop) -> Prop) f x).
Proof. exact (@lem3479739 A (type686 B) f x). Qed.
Lemma lem3479742 {A B : Type'} (t : type1413 A B) (x : A) : (term561 A B t x) = (term562 A B t x).
Proof. exact (MK_COMB (@lem3479726 B) (@lem3479734 A B t x)). Qed.
Lemma lem3479743 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (x : A) : (term268 A B t f x) = (term563 A B t f x).
Proof. exact (MK_COMB (@lem3479742 A B t x) (@lem3479741 A B f x)). Qed.
Lemma lem3479745 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3479746 {B : Type'} (f : type599 B) (x : B -> Prop) : (f x) = (@I ((B -> Prop) -> ((B -> Prop) -> Prop) -> Prop) f x).
Proof. exact (@lem3479745 (B -> Prop) (type180 B) f x). Qed.
Lemma lem3479747 {A B : Type'} (t : type1413 A B) (x : A) : (term562 A B t x) = (term564 A B t x).
Proof. exact (@lem3479746 B (@IN (B -> Prop)) (@I (A -> B -> Prop) t x)). Qed.
Lemma lem3479748 {A B : Type'} (f : type1374 A B) (x : A) : (@I (A -> (B -> Prop) -> Prop) f x) = (@I (A -> (B -> Prop) -> Prop) f x).
Proof. exact (eq_refl (@I (A -> (B -> Prop) -> Prop) f x)). Qed.
Lemma lem3479749 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (x : A) : (term563 A B t f x) = (term565 A B t f x).
Proof. exact (MK_COMB (@lem3479747 A B t x) (@lem3479748 A B f x)). Qed.
Lemma lem3479751 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3479752 {B : Type'} (f : type180 B) (x : type686 B) : (f x) = (@I (((B -> Prop) -> Prop) -> Prop) f x).
Proof. exact (@lem3479751 (type686 B) Prop f x). Qed.
Lemma lem3479753 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (x : A) : (term565 A B t f x) = (term566 A B t f x).
Proof. exact (@lem3479752 B (term564 A B t x) (@I (A -> (B -> Prop) -> Prop) f x)). Qed.
Lemma lem3479754 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (x : A) : (term563 A B t f x) = (term566 A B t f x).
Proof. exact (TRANS (@lem3479749 A B t f x) (@lem3479753 A B t f x)). Qed.
Lemma lem3479755 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (x : A) : (term268 A B t f x) = (term566 A B t f x).
Proof. exact (TRANS (@lem3479743 A B t f x) (@lem3479754 A B t f x)). Qed.
Lemma lem3479756 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3479757 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (x : A) : (term620 A B t f x) = (term621 A B t f x).
Proof. exact (MK_COMB (@lem3479756) (@lem3479755 A B t f x)). Qed.
Lemma lem3479758 {A B : Type'} (f : type1374 A B) (b : B) (t : type1413 A B) (x : A) : (term274 A B f b t x) = (term622 A B f b t x).
Proof. exact (MK_COMB (@lem3479757 A B t f x) (@lem3479725 A B b t x)). Qed.
Lemma lem3479759 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3479766 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3479767 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem3479766 A (type686 A) f x). Qed.
Lemma lem3479768 {A : Type'} (x : A) : (@IN A x) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x).
Proof. exact (@lem3479767 A (@IN A) x). Qed.
Lemma lem3479769 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem3479770 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x s).
Proof. exact (MK_COMB (@lem3479768 A x) (@lem3479769 A s)). Qed.
Lemma lem3479772 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3479773 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem3479772 (A -> Prop) Prop f x). Qed.
Lemma lem3479774 {A : Type'} (x : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x s) = (term553 A x s).
Proof. exact (@lem3479773 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x) s). Qed.
Lemma lem3479776 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (term553 A x s).
Proof. exact (TRANS (@lem3479770 A x s) (@lem3479774 A x s)). Qed.
Lemma lem3479777 {A : Type'} (x : A) (s : A -> Prop) : (term554 A x s) = (term555 A x s).
Proof. exact (MK_COMB (@lem3479759) (@lem3479776 A x s)). Qed.
Lemma lem3479778 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3479779 {A : Type'} (x : A) (s : A -> Prop) : (term556 A x s) = (term557 A x s).
Proof. exact (MK_COMB (@lem3479778) (@lem3479777 A x s)). Qed.
Lemma lem3479780 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) (t : type1413 A B) (x : A) : (term275 A B s f b t x) = (term623 A B s f b t x).
Proof. exact (MK_COMB (@lem3479779 A x s) (@lem3479758 A B f b t x)). Qed.
Lemma lem3479781 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) (t : type1413 A B) : (term285 A B s f b t) = (term624 A B s f b t).
Proof. exact (fun_ext (fun x : A => @lem3479780 A B s f b t x)). Qed.
Lemma lem3479782 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3479783 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) (t : type1413 A B) : (term286 A B s f b t) = (term625 A B s f b t).
Proof. exact (MK_COMB (@lem3479782 A) (@lem3479781 A B s f b t)). Qed.
Lemma lem3479784 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3479785 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) (t : type1413 A B) : (term409 A B s f b t) = (term626 A B s f b t).
Proof. exact (MK_COMB (@lem3479784) (@lem3479783 A B s f b t)). Qed.
Lemma lem3479786 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (x : type473 A B) : (term427 A B t f s b x) = (term627 A B t f s b x).
Proof. exact (MK_COMB (@lem3479785 A B s f b t) (@lem3479701 A B f s b x)). Qed.
Lemma lem3479787 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3479788 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (x : type473 A B) : (term524 A B t f s b x) = (term628 A B t f s b x).
Proof. exact (MK_COMB (@lem3479787) (@lem3479786 A B t f s b x)). Qed.
Lemma lem3479789 {A B : Type'} (t : type1413 A B) (x : type473 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (g : type1413 A B) : (term542 A B t x f s b g) = (term629 A B t x f s b g).
Proof. exact (MK_COMB (@lem3479788 A B t f s b x) (@lem3479561 A B x f s b g)). Qed.
Lemma lem3479790 {A B : Type'} (t : type1413 A B) (x : type473 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (g : type1413 A B) (h1 : term542 A B t x f s b g) : term629 A B t x f s b g.
Proof. exact (EQ_MP (@lem3479789 A B t x f s b g) (@lem3479338 A B t x f s b g h1)). Qed.
Lemma lem3479791 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (x : type473 A B) (h1 : term627 A B t f s b x) : term627 A B t f s b x.
Proof. exact (h1). Qed.
Lemma lem3479792 {A B : Type'} (x : type473 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (g : type1413 A B) (h1 : term610 A B x f s b g) : term610 A B x f s b g.
Proof. exact (h1). Qed.
Lemma lem3479793 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (x : type473 A B) (h1 : term627 A B t f s b x) : term619 A B f s b x.
Proof. exact (proj2 (@lem3479791 A B t f s b x h1)). Qed.
Lemma lem3479794 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (x : type473 A B) (h1 : term627 A B t f s b x) : term625 A B s f b t.
Proof. exact (proj1 (@lem3479791 A B t f s b x h1)). Qed.
Lemma lem3479795 {A B : Type'} (x : type473 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (g : type1413 A B) (h1 : term610 A B x f s b g) : term571 A B f s b g.
Proof. exact (proj2 (@lem3479792 A B x f s b g h1)). Qed.
Lemma lem3479796 {A B : Type'} (x : type473 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (g : type1413 A B) (h1 : term610 A B x f s b g) : term608 A B s f b x.
Proof. exact (proj1 (@lem3479792 A B x f s b g h1)). Qed.
Lemma lem3479797 {A B : Type'} (x : type473 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (g : type1413 A B) (h1 : term610 A B x f s b g) : term560 A B s b g.
Proof. exact (proj2 (@lem3479795 A B x f s b g h1)). Qed.
Lemma lem3479798 {A B : Type'} (x : type473 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (g : type1413 A B) (h1 : term610 A B x f s b g) : term569 A B s g f.
Proof. exact (proj1 (@lem3479795 A B x f s b g h1)). Qed.
Lemma lem3479816 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) (t : type1413 A B) (x : A) : (term623 A B s f b t x) = (term630 A B f s b t x).
Proof. exact (@lem19490 (term566 A B t f x) (term555 A x s) (term552 A B b t x)). Qed.
Lemma lem3479817 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) (t : type1413 A B) : (term624 A B s f b t) = (term631 A B f s b t).
Proof. exact (fun_ext (fun x : A => @lem3479816 A B f s b t x)). Qed.
Lemma lem3479818 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3479820 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) (t : type1413 A B) : (term625 A B s f b t) = (term632 A B f s b t).
Proof. exact (MK_COMB (@lem3479818 A) (@lem3479817 A B f s b t)). Qed.
Lemma lem3479821 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (x : type473 A B) (h1 : term627 A B t f s b x) : term632 A B f s b t.
Proof. exact (EQ_MP (@lem3479820 A B f s b t) (@lem3479794 A B t f s b x h1)). Qed.
Lemma lem3479836 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) (x : type473 A B) (g : type1413 A B) : (term617 A B f s b x g) = (term633 A B s f b x g).
Proof. exact (@lem19490 (term603 A B x g s) (term614 A B s f x g) (term580 A B b x g)). Qed.
Lemma lem3479843 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) (x : type473 A B) (g : type1413 A B) : (term634 A B s f b x g) = (term635 A B s f b x g).
Proof. exact (@lem19699 (term603 A B x g s) (term592 A B f x g) (term580 A B b x g)). Qed.
Lemma lem3479850 {A B : Type'} (f : type1374 A B) (x : type473 A B) (g : type1413 A B) (s : A -> Prop) : (term636 A B f x g s) = (term637 A B f x g s).
Proof. exact (@lem19699 (term603 A B x g s) (term592 A B f x g) (term603 A B x g s)). Qed.
Lemma lem3479851 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3479852 {A B : Type'} (f : type1374 A B) (x : type473 A B) (g : type1413 A B) (s : A -> Prop) : (term638 A B f x g s) = (term639 A B f x g s).
Proof. exact (MK_COMB (@lem3479851) (@lem3479850 A B f x g s)). Qed.
Lemma lem3479853 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) (x : type473 A B) (g : type1413 A B) : (term633 A B s f b x g) = (term640 A B s f b x g).
Proof. exact (MK_COMB (@lem3479852 A B f x g s) (@lem3479843 A B s f b x g)). Qed.
Lemma lem3479855 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) (x : type473 A B) (g : type1413 A B) : (term617 A B f s b x g) = (term640 A B s f b x g).
Proof. exact (TRANS (@lem3479836 A B s f b x g) (@lem3479853 A B s f b x g)). Qed.
Lemma lem3479856 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) (x : type473 A B) : (term618 A B f s b x) = (term641 A B s f b x).
Proof. exact (fun_ext (fun g : type1413 A B => @lem3479855 A B s f b x g)). Qed.
Lemma lem3479857 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem3479859 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) (x : type473 A B) : (term619 A B f s b x) = (term642 A B s f b x).
Proof. exact (MK_COMB (@lem3479857 A B) (@lem3479856 A B s f b x)). Qed.
Lemma lem3479860 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (x : type473 A B) (h1 : term627 A B t f s b x) : term642 A B s f b x.
Proof. exact (EQ_MP (@lem3479859 A B s f b x) (@lem3479793 A B t f s b x h1)). Qed.
Lemma lem3479872 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) (x : type473 A B) (t : type1413 A B) : (term606 A B s f b x t) = (term606 A B s f b x t).
Proof. exact (eq_refl (term606 A B s f b x t)). Qed.
Lemma lem3479873 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) (x : type473 A B) : (term607 A B s f b x) = (term607 A B s f b x).
Proof. exact (fun_ext (fun t : type1413 A B => @lem3479872 A B s f b x t)). Qed.
Lemma lem3479874 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem3479876 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) (x : type473 A B) : (term608 A B s f b x) = (term608 A B s f b x).
Proof. exact (MK_COMB (@lem3479874 A B) (@lem3479873 A B s f b x)). Qed.
Lemma lem3479877 {A B : Type'} (x : type473 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (g : type1413 A B) (h1 : term610 A B x f s b g) : term608 A B s f b x.
Proof. exact (EQ_MP (@lem3479876 A B s f b x) (@lem3479796 A B x f s b g h1)). Qed.
Lemma lem3479885 {A B : Type'} (s : A -> Prop) (g : type1413 A B) (f : type1374 A B) (x : A) : (term567 A B s g f x) = (term567 A B s g f x).
Proof. exact (eq_refl (term567 A B s g f x)). Qed.
Lemma lem3479886 {A B : Type'} (s : A -> Prop) (g : type1413 A B) (f : type1374 A B) : (term568 A B s g f) = (term568 A B s g f).
Proof. exact (fun_ext (fun x : A => @lem3479885 A B s g f x)). Qed.
Lemma lem3479887 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3479889 {A B : Type'} (s : A -> Prop) (g : type1413 A B) (f : type1374 A B) : (term569 A B s g f) = (term569 A B s g f).
Proof. exact (MK_COMB (@lem3479887 A) (@lem3479886 A B s g f)). Qed.
Lemma lem3479890 {A B : Type'} (x : type473 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (g : type1413 A B) (h1 : term610 A B x f s b g) : term569 A B s g f.
Proof. exact (EQ_MP (@lem3479889 A B s g f) (@lem3479798 A B x f s b g h1)). Qed.
Lemma lem3479898 {A B : Type'} (s : A -> Prop) (b : B) (g : type1413 A B) (x : A) : (term558 A B s b g x) = (term558 A B s b g x).
Proof. exact (eq_refl (term558 A B s b g x)). Qed.
Lemma lem3479899 {A B : Type'} (s : A -> Prop) (b : B) (g : type1413 A B) : (term559 A B s b g) = (term559 A B s b g).
Proof. exact (fun_ext (fun x : A => @lem3479898 A B s b g x)). Qed.
Lemma lem3479900 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3479902 {A B : Type'} (s : A -> Prop) (b : B) (g : type1413 A B) : (term560 A B s b g) = (term560 A B s b g).
Proof. exact (MK_COMB (@lem3479900 A) (@lem3479899 A B s b g)). Qed.
Lemma lem3479903 {A B : Type'} (x : type473 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (g : type1413 A B) (h1 : term610 A B x f s b g) : term560 A B s b g.
Proof. exact (EQ_MP (@lem3479902 A B s b g) (@lem3479797 A B x f s b g h1)). Qed.
Lemma lem3479904 {A B : Type'} (_36686 : A) (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (x : type473 A B) (h1 : term627 A B t f s b x) : term643 A B f s b t _36686.
Proof. exact (@lem3479821 A B t f s b x h1 _36686). Qed.
Lemma lem3479905 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) (t : type1413 A B) (_36686 : A) : (term643 A B f s b t _36686) = (term630 A B f s b t _36686).
Proof. exact (eq_refl (term643 A B f s b t _36686)). Qed.
Lemma lem3479906 {A B : Type'} (_36686 : A) (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (x : type473 A B) (h1 : term627 A B t f s b x) : term630 A B f s b t _36686.
Proof. exact (EQ_MP (@lem3479905 A B f s b t _36686) (@lem3479904 A B _36686 t f s b x h1)). Qed.
Lemma lem3479907 {A B : Type'} (_36687 : type1413 A B) (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (x : type473 A B) (h1 : term627 A B t f s b x) : term644 A B s f b x _36687.
Proof. exact (@lem3479860 A B t f s b x h1 _36687). Qed.
Lemma lem3479908 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) (x : type473 A B) (_36687 : type1413 A B) : (term644 A B s f b x _36687) = (term640 A B s f b x _36687).
Proof. exact (eq_refl (term644 A B s f b x _36687)). Qed.
Lemma lem3479909 {A B : Type'} (_36687 : type1413 A B) (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (x : type473 A B) (h1 : term627 A B t f s b x) : term640 A B s f b x _36687.
Proof. exact (EQ_MP (@lem3479908 A B s f b x _36687) (@lem3479907 A B _36687 t f s b x h1)). Qed.
Lemma lem3479910 {A B : Type'} (_36688 : type1413 A B) (x : type473 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (g : type1413 A B) (h1 : term610 A B x f s b g) : term645 A B s f b x _36688.
Proof. exact (@lem3479877 A B x f s b g h1 _36688). Qed.
Lemma lem3479911 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (b : B) (x : type473 A B) (_36688 : type1413 A B) : (term645 A B s f b x _36688) = (term606 A B s f b x _36688).
Proof. exact (eq_refl (term645 A B s f b x _36688)). Qed.
Lemma lem3479912 {A B : Type'} (_36688 : type1413 A B) (x : type473 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (g : type1413 A B) (h1 : term610 A B x f s b g) : term606 A B s f b x _36688.
Proof. exact (EQ_MP (@lem3479911 A B s f b x _36688) (@lem3479910 A B _36688 x f s b g h1)). Qed.
Lemma lem3479913 {A B : Type'} (_36689 : A) (x : type473 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (g : type1413 A B) (h1 : term610 A B x f s b g) : term646 A B s g f _36689.
Proof. exact (@lem3479890 A B x f s b g h1 _36689). Qed.
Lemma lem3479914 {A B : Type'} (s : A -> Prop) (g : type1413 A B) (f : type1374 A B) (_36689 : A) : (term646 A B s g f _36689) = (term567 A B s g f _36689).
Proof. exact (eq_refl (term646 A B s g f _36689)). Qed.
Lemma lem3479916 {A B : Type'} (_36690 : A) (x : type473 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (g : type1413 A B) (h1 : term610 A B x f s b g) : term647 A B s b g _36690.
Proof. exact (@lem3479903 A B x f s b g h1 _36690). Qed.
Lemma lem3479917 {A B : Type'} (s : A -> Prop) (b : B) (g : type1413 A B) (_36690 : A) : (term647 A B s b g _36690) = (term558 A B s b g _36690).
Proof. exact (eq_refl (term647 A B s b g _36690)). Qed.
Lemma lem3479919 {A B : Type'} (_36687 : type1413 A B) (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (x : type473 A B) (h1 : term627 A B t f s b x) : term635 A B s f b x _36687.
Proof. exact (proj2 (@lem3479909 A B _36687 t f s b x h1)). Qed.
Lemma lem3479920 {A B : Type'} (_36687 : type1413 A B) (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (x : type473 A B) (h1 : term627 A B t f s b x) : term637 A B f x _36687 s.
Proof. exact (proj1 (@lem3479909 A B _36687 t f s b x h1)). Qed.
Lemma lem3479940 {A B : Type'} (_36687 : type1413 A B) (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (x : type473 A B) (h1 : term627 A B t f s b x) : term596 A B f b x _36687.
Proof. exact (proj2 (@lem3479919 A B _36687 t f s b x h1)). Qed.
Lemma lem3479946 {A B : Type'} (_36687 : type1413 A B) (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (x : type473 A B) (h1 : term627 A B t f s b x) : term648 A B x _36687 s.
Proof. exact (proj1 (@lem3479920 A B _36687 t f s b x h1)). Qed.
Lemma lem3479958 {A B : Type'} (_36686 : A) (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (x : type473 A B) (h1 : term627 A B t f s b x) : term567 A B s t f _36686.
Proof. exact (proj1 (@lem3479906 A B _36686 t f s b x h1)). Qed.
Lemma lem3479964 {A B : Type'} (_36686 : A) (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (x : type473 A B) (h1 : term627 A B t f s b x) : term558 A B s b t _36686.
Proof. exact (proj2 (@lem3479906 A B _36686 t f s b x h1)). Qed.
Lemma lem3479970 {A B : Type'} (_36689 : A) (x : type473 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (g : type1413 A B) (h1 : term610 A B x f s b g) : term567 A B s g f _36689.
Proof. exact (EQ_MP (@lem3479914 A B s g f _36689) (@lem3479913 A B _36689 x f s b g h1)). Qed.
Lemma lem3479976 {A B : Type'} (_36690 : A) (x : type473 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (g : type1413 A B) (h1 : term610 A B x f s b g) : term558 A B s b g _36690.
Proof. exact (EQ_MP (@lem3479917 A B s b g _36690) (@lem3479916 A B _36690 x f s b g h1)). Qed.
Lemma lem3479984 {A B : Type'} (_36688 : type1413 A B) (x : type473 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (g : type1413 A B) (h1 : term610 A B x f s b g) : term596 A B f b x _36688.
Proof. exact (proj2 (@lem3479912 A B _36688 x f s b g h1)). Qed.
Lemma lem3479987 {A B : Type'} (x : type473 A B) (t : type1413 A B) (s : A -> Prop) (h1 : term649 A B x t s) : term649 A B x t s.
Proof. exact (h1). Qed.
Lemma lem3479988 {A B : Type'} (x : type473 A B) (t : type1413 A B) (s : A -> Prop) (h1 : term649 A B x t s) : term650 A B x t s.
Proof. exact (fun h0 : term603 A B x t s => @lem3479987 A B x t s h1). Qed.
Lemma lem3479990 (p : Prop) : (term651 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem3479991 {A B : Type'} (x : type473 A B) (t : type1413 A B) (s : A -> Prop) : (term650 A B x t s) = (term649 A B x t s).
Proof. exact (@lem3479990 (term603 A B x t s)). Qed.
Lemma lem3479992 {A B : Type'} (x : type473 A B) (t : type1413 A B) (s : A -> Prop) (h1 : term649 A B x t s) : term649 A B x t s.
Proof. exact (EQ_MP (@lem3479991 A B x t s) (@lem3479988 A B x t s h1)). Qed.
Lemma lem3479994 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3479995 (x : Prop) : (x = x) = True.
Proof. exact (@lem3479994 Prop x). Qed.
Lemma lem3479996 {A B : Type'} (x : type473 A B) (_36687 : type1413 A B) (s : A -> Prop) : ((term648 A B x _36687 s) = (term648 A B x _36687 s)) = True.
Proof. exact (@lem3479995 (term648 A B x _36687 s)). Qed.
Lemma lem3479997 {A B : Type'} (x : type473 A B) (_36687 : type1413 A B) (s : A -> Prop) : True = ((term648 A B x _36687 s) = (term648 A B x _36687 s)).
Proof. exact (SYM (@lem3479996 A B x _36687 s)). Qed.
Lemma lem3479998 {A B : Type'} (x : type473 A B) (_36687 : type1413 A B) (s : A -> Prop) : (term648 A B x _36687 s) = (term648 A B x _36687 s).
Proof. exact (EQ_MP (@lem3479997 A B x _36687 s) (@lem0)). Qed.
Lemma lem3479999 {A B : Type'} (_36687 : type1413 A B) (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (x : type473 A B) (h1 : term627 A B t f s b x) : term648 A B x _36687 s.
Proof. exact (EQ_MP (@lem3479998 A B x _36687 s) (@lem3479946 A B _36687 t f s b x h1)). Qed.
Lemma lem3480001 (b : Prop) (a : Prop) : (a \/ b) = (term652 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3480004 {A B : Type'} (x : type473 A B) (_36687 : type1413 A B) (s : A -> Prop) : (term648 A B x _36687 s) = (term653 A B x _36687 s).
Proof. exact (@lem3480001 (term603 A B x _36687 s) (term603 A B x _36687 s)). Qed.
Lemma lem3480007 {A B : Type'} (_36687 : type1413 A B) (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (x : type473 A B) (h1 : term627 A B t f s b x) : term653 A B x _36687 s.
Proof. exact (EQ_MP (@lem3480004 A B x _36687 s) (@lem3479999 A B _36687 t f s b x h1)). Qed.
Lemma lem3480008 {A B : Type'} (_36687 : type1413 A B) (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (x : type473 A B) (h1 : term627 A B t f s b x) : term653 A B x _36687 s.
Proof. exact (@lem3480007 A B _36687 t f s b x h1). Qed.
Lemma lem3480009 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (x : type473 A B) (h1 : term627 A B t f s b x) : term653 A B x t s.
Proof. exact (@lem3480008 A B t t f s b x h1). Qed.
Lemma lem3480012 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (x : type473 A B) (h1 : term649 A B x t s) (h2 : term627 A B t f s b x) : term603 A B x t s.
Proof. exact (@lem3480009 A B t f s b x h2 (@lem3479992 A B x t s h1)). Qed.
Lemma lem3480013 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (x : type473 A B) (h1 : term627 A B t f s b x) : term653 A B x t s.
Proof. exact (fun h0 : term649 A B x t s => @lem3480012 A B t f s b x h0 h1). Qed.
Lemma lem3480015 (p : Prop) : (term654 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3480016 {A B : Type'} (x : type473 A B) (t : type1413 A B) (s : A -> Prop) : (term653 A B x t s) = (term603 A B x t s).
Proof. exact (@lem3480015 (term603 A B x t s)). Qed.
Lemma lem3480017 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (x : type473 A B) (h1 : term627 A B t f s b x) : term603 A B x t s.
Proof. exact (EQ_MP (@lem3480016 A B x t s) (@lem3480013 A B t f s b x h1)). Qed.
Lemma lem3480023 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3480024 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (_36686 : A) (s : A -> Prop) : (term567 A B s t f _36686) = (term655 A B t f _36686 s).
Proof. exact (@lem3480023 (term566 A B t f _36686) (term555 A _36686 s)). Qed.
Lemma lem3480030 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3480031 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (_36686 : A) (s : A -> Prop) : (term656 A B s t f _36686) = (term657 A B t f _36686 s).
Proof. exact (MK_COMB (@lem3480030) (@lem3480024 A B t f _36686 s)). Qed.
Lemma lem3480037 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (_36686 : A) (s : A -> Prop) : (term655 A B t f _36686 s) = (term655 A B t f _36686 s).
Proof. exact (eq_refl (term655 A B t f _36686 s)). Qed.
Lemma lem3480038 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (_36686 : A) (s : A -> Prop) : ((term567 A B s t f _36686) = (term655 A B t f _36686 s)) = ((term655 A B t f _36686 s) = (term655 A B t f _36686 s)).
Proof. exact (MK_COMB (@lem3480031 A B t f _36686 s) (@lem3480037 A B t f _36686 s)). Qed.
Lemma lem3480040 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3480041 (x : Prop) : (x = x) = True.
Proof. exact (@lem3480040 Prop x). Qed.
Lemma lem3480042 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (_36686 : A) (s : A -> Prop) : ((term655 A B t f _36686 s) = (term655 A B t f _36686 s)) = True.
Proof. exact (@lem3480041 (term655 A B t f _36686 s)). Qed.
Lemma lem3480043 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (_36686 : A) (s : A -> Prop) : ((term567 A B s t f _36686) = (term655 A B t f _36686 s)) = True.
Proof. exact (TRANS (@lem3480038 A B t f _36686 s) (@lem3480042 A B t f _36686 s)). Qed.
Lemma lem3480044 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (_36686 : A) (s : A -> Prop) : True = ((term567 A B s t f _36686) = (term655 A B t f _36686 s)).
Proof. exact (SYM (@lem3480043 A B t f _36686 s)). Qed.
Lemma lem3480045 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (_36686 : A) (s : A -> Prop) : (term567 A B s t f _36686) = (term655 A B t f _36686 s).
Proof. exact (EQ_MP (@lem3480044 A B t f _36686 s) (@lem0)). Qed.
Lemma lem3480046 {A B : Type'} (_36686 : A) (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (x : type473 A B) (h1 : term627 A B t f s b x) : term655 A B t f _36686 s.
Proof. exact (EQ_MP (@lem3480045 A B t f _36686 s) (@lem3479958 A B _36686 t f s b x h1)). Qed.
Lemma lem3480048 (b : Prop) (a : Prop) : (a \/ b) = (term652 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3480049 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (f : type1374 A B) (_36686 : A) : (term655 A B t f _36686 s) = (term658 A B s t f _36686).
Proof. exact (@lem3480048 (term555 A _36686 s) (term566 A B t f _36686)). Qed.
Lemma lem3480051 (a : Prop) : (term249 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3480052 {A : Type'} (_36686 : A) (s : A -> Prop) : (term659 A _36686 s) = (term553 A _36686 s).
Proof. exact (@lem3480051 (term553 A _36686 s)). Qed.
Lemma lem3480053 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3480054 {A : Type'} (_36686 : A) (s : A -> Prop) : (term660 A _36686 s) = (term661 A _36686 s).
Proof. exact (MK_COMB (@lem3480053) (@lem3480052 A _36686 s)). Qed.
Lemma lem3480055 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (_36686 : A) : (term566 A B t f _36686) = (term566 A B t f _36686).
Proof. exact (eq_refl (term566 A B t f _36686)). Qed.
Lemma lem3480056 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (f : type1374 A B) (_36686 : A) : (term658 A B s t f _36686) = (term662 A B s t f _36686).
Proof. exact (MK_COMB (@lem3480054 A _36686 s) (@lem3480055 A B t f _36686)). Qed.
Lemma lem3480057 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (f : type1374 A B) (_36686 : A) : (term655 A B t f _36686 s) = (term662 A B s t f _36686).
Proof. exact (TRANS (@lem3480049 A B s t f _36686) (@lem3480056 A B s t f _36686)). Qed.
Lemma lem3480060 {A B : Type'} (_36686 : A) (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (x : type473 A B) (h1 : term627 A B t f s b x) : term662 A B s t f _36686.
Proof. exact (EQ_MP (@lem3480057 A B s t f _36686) (@lem3480046 A B _36686 t f s b x h1)). Qed.
Lemma lem3480061 {A B : Type'} (_36686 : A) (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (x : type473 A B) (h1 : term627 A B t f s b x) : term662 A B s t f _36686.
Proof. exact (@lem3480060 A B _36686 t f s b x h1). Qed.
Lemma lem3480062 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (x : type473 A B) (h1 : term627 A B t f s b x) : term663 A B s f x t.
Proof. exact (@lem3480061 A B (@I ((A -> B -> Prop) -> A) x t) t f s b x h1). Qed.
Lemma lem3480065 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (x : type473 A B) (h1 : term627 A B t f s b x) : term590 A B f x t.
Proof. exact (@lem3480062 A B t f s b x h1 (@lem3480017 A B t f s b x h1)). Qed.
Lemma lem3480066 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (x : type473 A B) (h1 : term627 A B t f s b x) : term664 A B f x t.
Proof. exact (fun h0 : term592 A B f x t => @lem3480065 A B t f s b x h1). Qed.
Lemma lem3480068 (p : Prop) : (term654 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3480069 {A B : Type'} (f : type1374 A B) (x : type473 A B) (t : type1413 A B) : (term664 A B f x t) = (term590 A B f x t).
Proof. exact (@lem3480068 (term590 A B f x t)). Qed.
Lemma lem3480070 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (x : type473 A B) (h1 : term627 A B t f s b x) : term590 A B f x t.
Proof. exact (EQ_MP (@lem3480069 A B f x t) (@lem3480066 A B t f s b x h1)). Qed.
Lemma lem3480073 {A B : Type'} (x : type473 A B) (t : type1413 A B) (s : A -> Prop) (h1 : term649 A B x t s) : term649 A B x t s.
Proof. exact (h1). Qed.
Lemma lem3480074 {A B : Type'} (x : type473 A B) (t : type1413 A B) (s : A -> Prop) (h1 : term649 A B x t s) : term650 A B x t s.
Proof. exact (fun h0 : term603 A B x t s => @lem3480073 A B x t s h1). Qed.
Lemma lem3480076 (p : Prop) : (term651 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem3480077 {A B : Type'} (x : type473 A B) (t : type1413 A B) (s : A -> Prop) : (term650 A B x t s) = (term649 A B x t s).
Proof. exact (@lem3480076 (term603 A B x t s)). Qed.
Lemma lem3480078 {A B : Type'} (x : type473 A B) (t : type1413 A B) (s : A -> Prop) (h1 : term649 A B x t s) : term649 A B x t s.
Proof. exact (EQ_MP (@lem3480077 A B x t s) (@lem3480074 A B x t s h1)). Qed.
Lemma lem3480080 {A B : Type'} (_36687 : type1413 A B) (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (x : type473 A B) (h1 : term627 A B t f s b x) : term653 A B x _36687 s.
Proof. exact (EQ_MP (@lem3480004 A B x _36687 s) (@lem3479999 A B _36687 t f s b x h1)). Qed.
Lemma lem3480081 {A B : Type'} (_36687 : type1413 A B) (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (x : type473 A B) (h1 : term627 A B t f s b x) : term653 A B x _36687 s.
Proof. exact (@lem3480080 A B _36687 t f s b x h1). Qed.
Lemma lem3480082 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (x : type473 A B) (h1 : term627 A B t f s b x) : term653 A B x t s.
Proof. exact (@lem3480081 A B t t f s b x h1). Qed.
Lemma lem3480085 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (x : type473 A B) (h1 : term649 A B x t s) (h2 : term627 A B t f s b x) : term603 A B x t s.
Proof. exact (@lem3480082 A B t f s b x h2 (@lem3480078 A B x t s h1)). Qed.
Lemma lem3480086 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (x : type473 A B) (h1 : term627 A B t f s b x) : term653 A B x t s.
Proof. exact (fun h0 : term649 A B x t s => @lem3480085 A B t f s b x h0 h1). Qed.
Lemma lem3480088 (p : Prop) : (term654 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3480089 {A B : Type'} (x : type473 A B) (t : type1413 A B) (s : A -> Prop) : (term653 A B x t s) = (term603 A B x t s).
Proof. exact (@lem3480088 (term603 A B x t s)). Qed.
Lemma lem3480090 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (x : type473 A B) (h1 : term627 A B t f s b x) : term603 A B x t s.
Proof. exact (EQ_MP (@lem3480089 A B x t s) (@lem3480086 A B t f s b x h1)). Qed.
Lemma lem3480096 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3480097 {A B : Type'} (b : B) (t : type1413 A B) (_36686 : A) (s : A -> Prop) : (term558 A B s b t _36686) = (term665 A B b t _36686 s).
Proof. exact (@lem3480096 (term552 A B b t _36686) (term555 A _36686 s)). Qed.
Lemma lem3480103 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3480104 {A B : Type'} (b : B) (t : type1413 A B) (_36686 : A) (s : A -> Prop) : (term666 A B s b t _36686) = (term667 A B b t _36686 s).
Proof. exact (MK_COMB (@lem3480103) (@lem3480097 A B b t _36686 s)). Qed.
Lemma lem3480110 {A B : Type'} (b : B) (t : type1413 A B) (_36686 : A) (s : A -> Prop) : (term665 A B b t _36686 s) = (term665 A B b t _36686 s).
Proof. exact (eq_refl (term665 A B b t _36686 s)). Qed.
Lemma lem3480111 {A B : Type'} (b : B) (t : type1413 A B) (_36686 : A) (s : A -> Prop) : ((term558 A B s b t _36686) = (term665 A B b t _36686 s)) = ((term665 A B b t _36686 s) = (term665 A B b t _36686 s)).
Proof. exact (MK_COMB (@lem3480104 A B b t _36686 s) (@lem3480110 A B b t _36686 s)). Qed.
Lemma lem3480113 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3480114 (x : Prop) : (x = x) = True.
Proof. exact (@lem3480113 Prop x). Qed.
Lemma lem3480115 {A B : Type'} (b : B) (t : type1413 A B) (_36686 : A) (s : A -> Prop) : ((term665 A B b t _36686 s) = (term665 A B b t _36686 s)) = True.
Proof. exact (@lem3480114 (term665 A B b t _36686 s)). Qed.
Lemma lem3480116 {A B : Type'} (b : B) (t : type1413 A B) (_36686 : A) (s : A -> Prop) : ((term558 A B s b t _36686) = (term665 A B b t _36686 s)) = True.
Proof. exact (TRANS (@lem3480111 A B b t _36686 s) (@lem3480115 A B b t _36686 s)). Qed.
Lemma lem3480117 {A B : Type'} (b : B) (t : type1413 A B) (_36686 : A) (s : A -> Prop) : True = ((term558 A B s b t _36686) = (term665 A B b t _36686 s)).
Proof. exact (SYM (@lem3480116 A B b t _36686 s)). Qed.
Lemma lem3480118 {A B : Type'} (b : B) (t : type1413 A B) (_36686 : A) (s : A -> Prop) : (term558 A B s b t _36686) = (term665 A B b t _36686 s).
Proof. exact (EQ_MP (@lem3480117 A B b t _36686 s) (@lem0)). Qed.
Lemma lem3480119 {A B : Type'} (_36686 : A) (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (x : type473 A B) (h1 : term627 A B t f s b x) : term665 A B b t _36686 s.
Proof. exact (EQ_MP (@lem3480118 A B b t _36686 s) (@lem3479964 A B _36686 t f s b x h1)). Qed.
Lemma lem3480121 (b : Prop) (a : Prop) : (a \/ b) = (term652 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3480122 {A B : Type'} (s : A -> Prop) (b : B) (t : type1413 A B) (_36686 : A) : (term665 A B b t _36686 s) = (term668 A B s b t _36686).
Proof. exact (@lem3480121 (term555 A _36686 s) (term552 A B b t _36686)). Qed.
Lemma lem3480124 (a : Prop) : (term249 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3480125 {A : Type'} (_36686 : A) (s : A -> Prop) : (term659 A _36686 s) = (term553 A _36686 s).
Proof. exact (@lem3480124 (term553 A _36686 s)). Qed.
Lemma lem3480126 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3480127 {A : Type'} (_36686 : A) (s : A -> Prop) : (term660 A _36686 s) = (term661 A _36686 s).
Proof. exact (MK_COMB (@lem3480126) (@lem3480125 A _36686 s)). Qed.
Lemma lem3480128 {A B : Type'} (b : B) (t : type1413 A B) (_36686 : A) : (term552 A B b t _36686) = (term552 A B b t _36686).
Proof. exact (eq_refl (term552 A B b t _36686)). Qed.
Lemma lem3480129 {A B : Type'} (s : A -> Prop) (b : B) (t : type1413 A B) (_36686 : A) : (term668 A B s b t _36686) = (term669 A B s b t _36686).
Proof. exact (MK_COMB (@lem3480127 A _36686 s) (@lem3480128 A B b t _36686)). Qed.
Lemma lem3480130 {A B : Type'} (s : A -> Prop) (b : B) (t : type1413 A B) (_36686 : A) : (term665 A B b t _36686 s) = (term669 A B s b t _36686).
Proof. exact (TRANS (@lem3480122 A B s b t _36686) (@lem3480129 A B s b t _36686)). Qed.
Lemma lem3480133 {A B : Type'} (_36686 : A) (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (x : type473 A B) (h1 : term627 A B t f s b x) : term669 A B s b t _36686.
Proof. exact (EQ_MP (@lem3480130 A B s b t _36686) (@lem3480119 A B _36686 t f s b x h1)). Qed.
Lemma lem3480134 {A B : Type'} (_36686 : A) (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (x : type473 A B) (h1 : term627 A B t f s b x) : term669 A B s b t _36686.
Proof. exact (@lem3480133 A B _36686 t f s b x h1). Qed.
Lemma lem3480135 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (x : type473 A B) (h1 : term627 A B t f s b x) : term670 A B s b x t.
Proof. exact (@lem3480134 A B (@I ((A -> B -> Prop) -> A) x t) t f s b x h1). Qed.
Lemma lem3480138 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (x : type473 A B) (h1 : term627 A B t f s b x) : term578 A B b x t.
Proof. exact (@lem3480135 A B t f s b x h1 (@lem3480090 A B t f s b x h1)). Qed.
Lemma lem3480139 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (x : type473 A B) (h1 : term627 A B t f s b x) : term671 A B b x t.
Proof. exact (fun h0 : term580 A B b x t => @lem3480138 A B t f s b x h1). Qed.
Lemma lem3480141 (p : Prop) : (term654 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3480142 {A B : Type'} (b : B) (x : type473 A B) (t : type1413 A B) : (term671 A B b x t) = (term578 A B b x t).
Proof. exact (@lem3480141 (term578 A B b x t)). Qed.
Lemma lem3480143 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (x : type473 A B) (h1 : term627 A B t f s b x) : term578 A B b x t.
Proof. exact (EQ_MP (@lem3480142 A B b x t) (@lem3480139 A B t f s b x h1)). Qed.
Lemma lem3480145 (a : Prop) (b : Prop) : (term672 a b) = (term673 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3480146 {A B : Type'} (f : type1374 A B) (b : B) (x : type473 A B) (_36687 : type1413 A B) : (term596 A B f b x _36687) = (term674 A B f b x _36687).
Proof. exact (@lem3480145 (term590 A B f x _36687) (term578 A B b x _36687)). Qed.
Lemma lem3480148 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3480149 {A B : Type'} (f : type1374 A B) (b : B) (x : type473 A B) (_36687 : type1413 A B) : (term674 A B f b x _36687) = (term675 A B f b x _36687).
Proof. exact (@lem3480148 (term676 A B f b x _36687)). Qed.
Lemma lem3480150 {A B : Type'} (f : type1374 A B) (b : B) (x : type473 A B) (_36687 : type1413 A B) : (term596 A B f b x _36687) = (term675 A B f b x _36687).
Proof. exact (TRANS (@lem3480146 A B f b x _36687) (@lem3480149 A B f b x _36687)). Qed.
Lemma lem3480152 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (x : type473 A B) (h1 : term627 A B t f s b x) : term676 A B f b x t.
Proof. exact (conj (@lem3480070 A B t f s b x h1) (@lem3480143 A B t f s b x h1)). Qed.
Lemma lem3480154 {A B : Type'} (_36687 : type1413 A B) (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (x : type473 A B) (h1 : term627 A B t f s b x) : term675 A B f b x _36687.
Proof. exact (EQ_MP (@lem3480150 A B f b x _36687) (@lem3479940 A B _36687 t f s b x h1)). Qed.
Lemma lem3480155 {A B : Type'} (_36687 : type1413 A B) (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (x : type473 A B) (h1 : term627 A B t f s b x) : term675 A B f b x _36687.
Proof. exact (@lem3480154 A B _36687 t f s b x h1). Qed.
Lemma lem3480156 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (x : type473 A B) (h1 : term627 A B t f s b x) : term675 A B f b x t.
Proof. exact (@lem3480155 A B t t f s b x h1). Qed.
Lemma lem3480159 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (x : type473 A B) (h1 : term627 A B t f s b x) : False.
Proof. exact (@lem3480156 A B t f s b x h1 (@lem3480152 A B t f s b x h1)). Qed.
Lemma lem3480160 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (x : type473 A B) (h1 : term627 A B t f s b x) : term677.
Proof. exact (fun h0 : ~ False => @lem3480159 A B t f s b x h1). Qed.
Lemma lem3480162 (p : Prop) : (term654 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3480163 : term677 = False.
Proof. exact (@lem3480162 False). Qed.
Lemma lem3480164 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (x : type473 A B) (h1 : term627 A B t f s b x) : False.
Proof. exact (EQ_MP (@lem3480163) (@lem3480160 A B t f s b x h1)). Qed.
Lemma lem3480166 {A B : Type'} (_36688 : type1413 A B) (x : type473 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (g : type1413 A B) (h1 : term610 A B x f s b g) : term603 A B x _36688 s.
Proof. exact (proj1 (@lem3479912 A B _36688 x f s b g h1)). Qed.
Lemma lem3480167 {A B : Type'} (_36688 : type1413 A B) (x : type473 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (g : type1413 A B) (h1 : term610 A B x f s b g) : term603 A B x _36688 s.
Proof. exact (@lem3480166 A B _36688 x f s b g h1). Qed.
Lemma lem3480168 {A B : Type'} (x : type473 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (g : type1413 A B) (h1 : term610 A B x f s b g) : term603 A B x g s.
Proof. exact (@lem3480167 A B g x f s b g h1). Qed.
Lemma lem3480169 {A B : Type'} (x : type473 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (g : type1413 A B) (h1 : term610 A B x f s b g) : term653 A B x g s.
Proof. exact (fun h0 : term649 A B x g s => @lem3480168 A B x f s b g h1). Qed.
Lemma lem3480171 (p : Prop) : (term654 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3480172 {A B : Type'} (x : type473 A B) (g : type1413 A B) (s : A -> Prop) : (term653 A B x g s) = (term603 A B x g s).
Proof. exact (@lem3480171 (term603 A B x g s)). Qed.
Lemma lem3480173 {A B : Type'} (x : type473 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (g : type1413 A B) (h1 : term610 A B x f s b g) : term603 A B x g s.
Proof. exact (EQ_MP (@lem3480172 A B x g s) (@lem3480169 A B x f s b g h1)). Qed.
Lemma lem3480179 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3480180 {A B : Type'} (g : type1413 A B) (f : type1374 A B) (_36689 : A) (s : A -> Prop) : (term567 A B s g f _36689) = (term655 A B g f _36689 s).
Proof. exact (@lem3480179 (term566 A B g f _36689) (term555 A _36689 s)). Qed.
Lemma lem3480186 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3480187 {A B : Type'} (g : type1413 A B) (f : type1374 A B) (_36689 : A) (s : A -> Prop) : (term656 A B s g f _36689) = (term657 A B g f _36689 s).
Proof. exact (MK_COMB (@lem3480186) (@lem3480180 A B g f _36689 s)). Qed.
Lemma lem3480193 {A B : Type'} (g : type1413 A B) (f : type1374 A B) (_36689 : A) (s : A -> Prop) : (term655 A B g f _36689 s) = (term655 A B g f _36689 s).
Proof. exact (eq_refl (term655 A B g f _36689 s)). Qed.
Lemma lem3480194 {A B : Type'} (g : type1413 A B) (f : type1374 A B) (_36689 : A) (s : A -> Prop) : ((term567 A B s g f _36689) = (term655 A B g f _36689 s)) = ((term655 A B g f _36689 s) = (term655 A B g f _36689 s)).
Proof. exact (MK_COMB (@lem3480187 A B g f _36689 s) (@lem3480193 A B g f _36689 s)). Qed.
Lemma lem3480196 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3480197 (x : Prop) : (x = x) = True.
Proof. exact (@lem3480196 Prop x). Qed.
Lemma lem3480198 {A B : Type'} (g : type1413 A B) (f : type1374 A B) (_36689 : A) (s : A -> Prop) : ((term655 A B g f _36689 s) = (term655 A B g f _36689 s)) = True.
Proof. exact (@lem3480197 (term655 A B g f _36689 s)). Qed.
Lemma lem3480199 {A B : Type'} (g : type1413 A B) (f : type1374 A B) (_36689 : A) (s : A -> Prop) : ((term567 A B s g f _36689) = (term655 A B g f _36689 s)) = True.
Proof. exact (TRANS (@lem3480194 A B g f _36689 s) (@lem3480198 A B g f _36689 s)). Qed.
Lemma lem3480200 {A B : Type'} (g : type1413 A B) (f : type1374 A B) (_36689 : A) (s : A -> Prop) : True = ((term567 A B s g f _36689) = (term655 A B g f _36689 s)).
Proof. exact (SYM (@lem3480199 A B g f _36689 s)). Qed.
Lemma lem3480201 {A B : Type'} (g : type1413 A B) (f : type1374 A B) (_36689 : A) (s : A -> Prop) : (term567 A B s g f _36689) = (term655 A B g f _36689 s).
Proof. exact (EQ_MP (@lem3480200 A B g f _36689 s) (@lem0)). Qed.
Lemma lem3480202 {A B : Type'} (_36689 : A) (x : type473 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (g : type1413 A B) (h1 : term610 A B x f s b g) : term655 A B g f _36689 s.
Proof. exact (EQ_MP (@lem3480201 A B g f _36689 s) (@lem3479970 A B _36689 x f s b g h1)). Qed.
Lemma lem3480204 (b : Prop) (a : Prop) : (a \/ b) = (term652 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3480205 {A B : Type'} (s : A -> Prop) (g : type1413 A B) (f : type1374 A B) (_36689 : A) : (term655 A B g f _36689 s) = (term658 A B s g f _36689).
Proof. exact (@lem3480204 (term555 A _36689 s) (term566 A B g f _36689)). Qed.
Lemma lem3480207 (a : Prop) : (term249 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3480208 {A : Type'} (_36689 : A) (s : A -> Prop) : (term659 A _36689 s) = (term553 A _36689 s).
Proof. exact (@lem3480207 (term553 A _36689 s)). Qed.
Lemma lem3480209 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3480210 {A : Type'} (_36689 : A) (s : A -> Prop) : (term660 A _36689 s) = (term661 A _36689 s).
Proof. exact (MK_COMB (@lem3480209) (@lem3480208 A _36689 s)). Qed.
Lemma lem3480211 {A B : Type'} (g : type1413 A B) (f : type1374 A B) (_36689 : A) : (term566 A B g f _36689) = (term566 A B g f _36689).
Proof. exact (eq_refl (term566 A B g f _36689)). Qed.
Lemma lem3480212 {A B : Type'} (s : A -> Prop) (g : type1413 A B) (f : type1374 A B) (_36689 : A) : (term658 A B s g f _36689) = (term662 A B s g f _36689).
Proof. exact (MK_COMB (@lem3480210 A _36689 s) (@lem3480211 A B g f _36689)). Qed.
Lemma lem3480213 {A B : Type'} (s : A -> Prop) (g : type1413 A B) (f : type1374 A B) (_36689 : A) : (term655 A B g f _36689 s) = (term662 A B s g f _36689).
Proof. exact (TRANS (@lem3480205 A B s g f _36689) (@lem3480212 A B s g f _36689)). Qed.
Lemma lem3480216 {A B : Type'} (_36689 : A) (x : type473 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (g : type1413 A B) (h1 : term610 A B x f s b g) : term662 A B s g f _36689.
Proof. exact (EQ_MP (@lem3480213 A B s g f _36689) (@lem3480202 A B _36689 x f s b g h1)). Qed.
Lemma lem3480217 {A B : Type'} (_36689 : A) (x : type473 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (g : type1413 A B) (h1 : term610 A B x f s b g) : term662 A B s g f _36689.
Proof. exact (@lem3480216 A B _36689 x f s b g h1). Qed.
Lemma lem3480218 {A B : Type'} (x : type473 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (g : type1413 A B) (h1 : term610 A B x f s b g) : term663 A B s f x g.
Proof. exact (@lem3480217 A B (@I ((A -> B -> Prop) -> A) x g) x f s b g h1). Qed.
Lemma lem3480221 {A B : Type'} (x : type473 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (g : type1413 A B) (h1 : term610 A B x f s b g) : term590 A B f x g.
Proof. exact (@lem3480218 A B x f s b g h1 (@lem3480173 A B x f s b g h1)). Qed.
Lemma lem3480222 {A B : Type'} (x : type473 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (g : type1413 A B) (h1 : term610 A B x f s b g) : term664 A B f x g.
Proof. exact (fun h0 : term592 A B f x g => @lem3480221 A B x f s b g h1). Qed.
Lemma lem3480224 (p : Prop) : (term654 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3480225 {A B : Type'} (f : type1374 A B) (x : type473 A B) (g : type1413 A B) : (term664 A B f x g) = (term590 A B f x g).
Proof. exact (@lem3480224 (term590 A B f x g)). Qed.
Lemma lem3480226 {A B : Type'} (x : type473 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (g : type1413 A B) (h1 : term610 A B x f s b g) : term590 A B f x g.
Proof. exact (EQ_MP (@lem3480225 A B f x g) (@lem3480222 A B x f s b g h1)). Qed.
Lemma lem3480228 {A B : Type'} (_36688 : type1413 A B) (x : type473 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (g : type1413 A B) (h1 : term610 A B x f s b g) : term603 A B x _36688 s.
Proof. exact (proj1 (@lem3479912 A B _36688 x f s b g h1)). Qed.
Lemma lem3480229 {A B : Type'} (_36688 : type1413 A B) (x : type473 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (g : type1413 A B) (h1 : term610 A B x f s b g) : term603 A B x _36688 s.
Proof. exact (@lem3480228 A B _36688 x f s b g h1). Qed.
Lemma lem3480230 {A B : Type'} (x : type473 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (g : type1413 A B) (h1 : term610 A B x f s b g) : term603 A B x g s.
Proof. exact (@lem3480229 A B g x f s b g h1). Qed.
Lemma lem3480231 {A B : Type'} (x : type473 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (g : type1413 A B) (h1 : term610 A B x f s b g) : term653 A B x g s.
Proof. exact (fun h0 : term649 A B x g s => @lem3480230 A B x f s b g h1). Qed.
Lemma lem3480233 (p : Prop) : (term654 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3480234 {A B : Type'} (x : type473 A B) (g : type1413 A B) (s : A -> Prop) : (term653 A B x g s) = (term603 A B x g s).
Proof. exact (@lem3480233 (term603 A B x g s)). Qed.
Lemma lem3480235 {A B : Type'} (x : type473 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (g : type1413 A B) (h1 : term610 A B x f s b g) : term603 A B x g s.
Proof. exact (EQ_MP (@lem3480234 A B x g s) (@lem3480231 A B x f s b g h1)). Qed.
Lemma lem3480241 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3480242 {A B : Type'} (b : B) (g : type1413 A B) (_36690 : A) (s : A -> Prop) : (term558 A B s b g _36690) = (term665 A B b g _36690 s).
Proof. exact (@lem3480241 (term552 A B b g _36690) (term555 A _36690 s)). Qed.
Lemma lem3480248 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3480249 {A B : Type'} (b : B) (g : type1413 A B) (_36690 : A) (s : A -> Prop) : (term666 A B s b g _36690) = (term667 A B b g _36690 s).
Proof. exact (MK_COMB (@lem3480248) (@lem3480242 A B b g _36690 s)). Qed.
Lemma lem3480255 {A B : Type'} (b : B) (g : type1413 A B) (_36690 : A) (s : A -> Prop) : (term665 A B b g _36690 s) = (term665 A B b g _36690 s).
Proof. exact (eq_refl (term665 A B b g _36690 s)). Qed.
Lemma lem3480256 {A B : Type'} (b : B) (g : type1413 A B) (_36690 : A) (s : A -> Prop) : ((term558 A B s b g _36690) = (term665 A B b g _36690 s)) = ((term665 A B b g _36690 s) = (term665 A B b g _36690 s)).
Proof. exact (MK_COMB (@lem3480249 A B b g _36690 s) (@lem3480255 A B b g _36690 s)). Qed.
Lemma lem3480258 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3480259 (x : Prop) : (x = x) = True.
Proof. exact (@lem3480258 Prop x). Qed.
Lemma lem3480260 {A B : Type'} (b : B) (g : type1413 A B) (_36690 : A) (s : A -> Prop) : ((term665 A B b g _36690 s) = (term665 A B b g _36690 s)) = True.
Proof. exact (@lem3480259 (term665 A B b g _36690 s)). Qed.
Lemma lem3480261 {A B : Type'} (b : B) (g : type1413 A B) (_36690 : A) (s : A -> Prop) : ((term558 A B s b g _36690) = (term665 A B b g _36690 s)) = True.
Proof. exact (TRANS (@lem3480256 A B b g _36690 s) (@lem3480260 A B b g _36690 s)). Qed.
Lemma lem3480262 {A B : Type'} (b : B) (g : type1413 A B) (_36690 : A) (s : A -> Prop) : True = ((term558 A B s b g _36690) = (term665 A B b g _36690 s)).
Proof. exact (SYM (@lem3480261 A B b g _36690 s)). Qed.
Lemma lem3480263 {A B : Type'} (b : B) (g : type1413 A B) (_36690 : A) (s : A -> Prop) : (term558 A B s b g _36690) = (term665 A B b g _36690 s).
Proof. exact (EQ_MP (@lem3480262 A B b g _36690 s) (@lem0)). Qed.
Lemma lem3480264 {A B : Type'} (_36690 : A) (x : type473 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (g : type1413 A B) (h1 : term610 A B x f s b g) : term665 A B b g _36690 s.
Proof. exact (EQ_MP (@lem3480263 A B b g _36690 s) (@lem3479976 A B _36690 x f s b g h1)). Qed.
Lemma lem3480266 (b : Prop) (a : Prop) : (a \/ b) = (term652 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3480267 {A B : Type'} (s : A -> Prop) (b : B) (g : type1413 A B) (_36690 : A) : (term665 A B b g _36690 s) = (term668 A B s b g _36690).
Proof. exact (@lem3480266 (term555 A _36690 s) (term552 A B b g _36690)). Qed.
Lemma lem3480269 (a : Prop) : (term249 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3480270 {A : Type'} (_36690 : A) (s : A -> Prop) : (term659 A _36690 s) = (term553 A _36690 s).
Proof. exact (@lem3480269 (term553 A _36690 s)). Qed.
Lemma lem3480271 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3480272 {A : Type'} (_36690 : A) (s : A -> Prop) : (term660 A _36690 s) = (term661 A _36690 s).
Proof. exact (MK_COMB (@lem3480271) (@lem3480270 A _36690 s)). Qed.
Lemma lem3480273 {A B : Type'} (b : B) (g : type1413 A B) (_36690 : A) : (term552 A B b g _36690) = (term552 A B b g _36690).
Proof. exact (eq_refl (term552 A B b g _36690)). Qed.
Lemma lem3480274 {A B : Type'} (s : A -> Prop) (b : B) (g : type1413 A B) (_36690 : A) : (term668 A B s b g _36690) = (term669 A B s b g _36690).
Proof. exact (MK_COMB (@lem3480272 A _36690 s) (@lem3480273 A B b g _36690)). Qed.
Lemma lem3480275 {A B : Type'} (s : A -> Prop) (b : B) (g : type1413 A B) (_36690 : A) : (term665 A B b g _36690 s) = (term669 A B s b g _36690).
Proof. exact (TRANS (@lem3480267 A B s b g _36690) (@lem3480274 A B s b g _36690)). Qed.
Lemma lem3480278 {A B : Type'} (_36690 : A) (x : type473 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (g : type1413 A B) (h1 : term610 A B x f s b g) : term669 A B s b g _36690.
Proof. exact (EQ_MP (@lem3480275 A B s b g _36690) (@lem3480264 A B _36690 x f s b g h1)). Qed.
Lemma lem3480279 {A B : Type'} (_36690 : A) (x : type473 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (g : type1413 A B) (h1 : term610 A B x f s b g) : term669 A B s b g _36690.
Proof. exact (@lem3480278 A B _36690 x f s b g h1). Qed.
Lemma lem3480280 {A B : Type'} (x : type473 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (g : type1413 A B) (h1 : term610 A B x f s b g) : term670 A B s b x g.
Proof. exact (@lem3480279 A B (@I ((A -> B -> Prop) -> A) x g) x f s b g h1). Qed.
Lemma lem3480283 {A B : Type'} (x : type473 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (g : type1413 A B) (h1 : term610 A B x f s b g) : term578 A B b x g.
Proof. exact (@lem3480280 A B x f s b g h1 (@lem3480235 A B x f s b g h1)). Qed.
Lemma lem3480284 {A B : Type'} (x : type473 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (g : type1413 A B) (h1 : term610 A B x f s b g) : term671 A B b x g.
Proof. exact (fun h0 : term580 A B b x g => @lem3480283 A B x f s b g h1). Qed.
Lemma lem3480286 (p : Prop) : (term654 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3480287 {A B : Type'} (b : B) (x : type473 A B) (g : type1413 A B) : (term671 A B b x g) = (term578 A B b x g).
Proof. exact (@lem3480286 (term578 A B b x g)). Qed.
Lemma lem3480288 {A B : Type'} (x : type473 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (g : type1413 A B) (h1 : term610 A B x f s b g) : term578 A B b x g.
Proof. exact (EQ_MP (@lem3480287 A B b x g) (@lem3480284 A B x f s b g h1)). Qed.
Lemma lem3480290 (a : Prop) (b : Prop) : (term672 a b) = (term673 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3480291 {A B : Type'} (f : type1374 A B) (b : B) (x : type473 A B) (_36688 : type1413 A B) : (term596 A B f b x _36688) = (term674 A B f b x _36688).
Proof. exact (@lem3480290 (term590 A B f x _36688) (term578 A B b x _36688)). Qed.
Lemma lem3480293 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3480294 {A B : Type'} (f : type1374 A B) (b : B) (x : type473 A B) (_36688 : type1413 A B) : (term674 A B f b x _36688) = (term675 A B f b x _36688).
Proof. exact (@lem3480293 (term676 A B f b x _36688)). Qed.
Lemma lem3480295 {A B : Type'} (f : type1374 A B) (b : B) (x : type473 A B) (_36688 : type1413 A B) : (term596 A B f b x _36688) = (term675 A B f b x _36688).
Proof. exact (TRANS (@lem3480291 A B f b x _36688) (@lem3480294 A B f b x _36688)). Qed.
Lemma lem3480297 {A B : Type'} (x : type473 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (g : type1413 A B) (h1 : term610 A B x f s b g) : term676 A B f b x g.
Proof. exact (conj (@lem3480226 A B x f s b g h1) (@lem3480288 A B x f s b g h1)). Qed.
Lemma lem3480299 {A B : Type'} (_36688 : type1413 A B) (x : type473 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (g : type1413 A B) (h1 : term610 A B x f s b g) : term675 A B f b x _36688.
Proof. exact (EQ_MP (@lem3480295 A B f b x _36688) (@lem3479984 A B _36688 x f s b g h1)). Qed.
Lemma lem3480300 {A B : Type'} (_36688 : type1413 A B) (x : type473 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (g : type1413 A B) (h1 : term610 A B x f s b g) : term675 A B f b x _36688.
Proof. exact (@lem3480299 A B _36688 x f s b g h1). Qed.
Lemma lem3480301 {A B : Type'} (x : type473 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (g : type1413 A B) (h1 : term610 A B x f s b g) : term675 A B f b x g.
Proof. exact (@lem3480300 A B g x f s b g h1). Qed.
Lemma lem3480304 {A B : Type'} (x : type473 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (g : type1413 A B) (h1 : term610 A B x f s b g) : False.
Proof. exact (@lem3480301 A B x f s b g h1 (@lem3480297 A B x f s b g h1)). Qed.
Lemma lem3480305 {A B : Type'} (x : type473 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (g : type1413 A B) (h1 : term610 A B x f s b g) : term677.
Proof. exact (fun h0 : ~ False => @lem3480304 A B x f s b g h1). Qed.
Lemma lem3480307 (p : Prop) : (term654 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3480308 : term677 = False.
Proof. exact (@lem3480307 False). Qed.
Lemma lem3480309 {A B : Type'} (x : type473 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (g : type1413 A B) (h1 : term610 A B x f s b g) : False.
Proof. exact (EQ_MP (@lem3480308) (@lem3480305 A B x f s b g h1)). Qed.
Lemma lem3480310 {A B : Type'} (t : type1413 A B) (x : type473 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (g : type1413 A B) (h1 : term542 A B t x f s b g) : False.
Proof. exact (or_elim (@lem3479790 A B t x f s b g h1) (fun h0 : term627 A B t f s b x => @lem3480164 A B t f s b x h0) (fun h0 : term610 A B x f s b g => @lem3480309 A B x f s b g h0)). Qed.
Lemma lem3480311 {A B : Type'} (t : type1413 A B) (x : type473 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (h1 : term545 A B t x f s b) : False.
Proof. exact (ex_elim (@lem3479337 A B t x f s b h1) (fun g : type1413 A B => fun h0 : term544 A B t x f s b g => @lem3480310 A B t x f s b g h0)). Qed.
Lemma lem3480312 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (b : B) (h1 : term547 A B t f s b) : False.
Proof. exact (ex_elim (@lem3479336 A B t f s b h1) (fun x : type473 A B => fun h0 : term546 A B t f s b x => @lem3480311 A B t x f s b h0)). Qed.
Lemma lem3480313 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) (h1 : term244 A B f s b) : False.
Proof. exact (ex_elim (@lem3479335 A B f s b h1) (fun t : type1413 A B => fun h0 : term548 A B f s b t => @lem3480312 A B t f s b h0)). Qed.
Lemma lem3480314 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) (h1 : term244 A B f s b) : (term244 A B f s b) = False.
Proof. exact (prop_ext (fun h2 : term244 A B f s b => @lem3480313 A B f s b h1) (fun h2 : False => @lem3478523 A B f s b h1)). Qed.
Lemma lem3480315 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) (h1 : term244 A B f s b) : False.
Proof. exact (EQ_MP (@lem3480314 A B f s b h1) (@lem3478523 A B f s b h1)). Qed.
Lemma lem3480316 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : term243 A B f s b.
Proof. exact (fun h0 : term244 A B f s b => @lem3480315 A B f s b h0). Qed.
Lemma lem3480317 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : (term240 A B s f b) = (term197 A B f s b).
Proof. exact (EQ_MP (@lem3478522 A B f s b) (@lem3480316 A B f s b)). Qed.
Lemma lem3480322 {A B : Type'} (s : A -> Prop) (b : B) : term253 A B s b.
Proof. exact (fun f : type1374 A B => @lem3480317 A B f s b). Qed.
Lemma lem3480327 {A B : Type'} (b : B) : term257 A B b.
Proof. exact (fun s : A -> Prop => @lem3480322 A B s b). Qed.
Lemma lem3480332 {A B : Type'} : term261 A B.
Proof. exact (fun b : B => @lem3480327 A B b). Qed.
Lemma lem3480333 {A B : Type'} : term260 A B.
Proof. exact (EQ_MP (@lem3478518 A B) (@lem3480332 A B)). Qed.
Lemma lem3480334 {A B : Type'} (b : B) : term678 A B b.
Proof. exact (@lem3480333 A B b). Qed.
Lemma lem3480335 {A B : Type'} (b : B) : (term678 A B b) = (term256 A B b).
Proof. exact (eq_refl (term678 A B b)). Qed.
Lemma lem3480336 {A B : Type'} (b : B) : term256 A B b.
Proof. exact (EQ_MP (@lem3480335 A B b) (@lem3480334 A B b)). Qed.
Lemma lem3480337 {A B : Type'} (b : B) (s : A -> Prop) : term679 A B b s.
Proof. exact (@lem3480336 A B b s). Qed.
Lemma lem3480338 {A B : Type'} (s : A -> Prop) (b : B) : (term679 A B b s) = (term252 A B s b).
Proof. exact (eq_refl (term679 A B b s)). Qed.
Lemma lem3480339 {A B : Type'} (s : A -> Prop) (b : B) : term252 A B s b.
Proof. exact (EQ_MP (@lem3480338 A B s b) (@lem3480337 A B b s)). Qed.
Lemma lem3480340 {A B : Type'} (s : A -> Prop) (b : B) (f : type1374 A B) : term680 A B s b f.
Proof. exact (@lem3480339 A B s b f). Qed.
Lemma lem3480341 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : (term680 A B s b f) = (term243 A B f s b).
Proof. exact (eq_refl (term680 A B s b f)). Qed.
Lemma lem3480342 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : term243 A B f s b.
Proof. exact (EQ_MP (@lem3480341 A B f s b) (@lem3480340 A B s b f)). Qed.
Lemma lem3480344 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : term243 A B f s b.
Proof. exact (@lem3478289 A B f s b (@lem3480342 A B f s b)). Qed.
Lemma lem3480345 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) (h1 : term244 A B f s b) : False.
Proof. exact (@lem3480344 A B f s b (@lem3478273 A B f s b h1)). Qed.
Lemma lem3480346 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) (h1 : term244 A B f s b) : (term244 A B f s b) = False.
Proof. exact (prop_ext (fun h2 : term244 A B f s b => @lem3480345 A B f s b h1) (fun h2 : False => @lem3478273 A B f s b h1)). Qed.
Lemma lem3480347 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) (h1 : term244 A B f s b) : False.
Proof. exact (EQ_MP (@lem3480346 A B f s b h1) (@lem3478273 A B f s b h1)). Qed.
Lemma lem3480348 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : term243 A B f s b.
Proof. exact (fun h0 : term244 A B f s b => @lem3480347 A B f s b h0). Qed.
Lemma lem3480349 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : (term240 A B s f b) = (term197 A B f s b).
Proof. exact (EQ_MP (@lem3478272 A B f s b) (@lem3480348 A B f s b)). Qed.
Lemma lem3480350 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (b : B) : (term165 A B s f b) = (term197 A B f s b).
Proof. exact (EQ_MP (@lem3478268 A B f s b) (@lem3480349 A B f s b)). Qed.
Lemma lem3480355 {A B : Type'} (f : type1374 A B) (s : A -> Prop) : term199 A B f s.
Proof. exact (fun b : B => @lem3480350 A B f s b). Qed.
Lemma lem3480356 {A B : Type'} (f : type1374 A B) (s : A -> Prop) : term151 A B f s.
Proof. exact (EQ_MP (@lem3478163 A B f s) (@lem3480355 A B f s)). Qed.
Lemma lem3480357 {A B : Type'} (f : type1374 A B) (s : A -> Prop) : term39 A B f s.
Proof. exact (EQ_MP (@lem3478020 A B f s) (@lem3480356 A B f s)). Qed.
Lemma lem3480358 {A B : Type'} (f : type1374 A B) (s : A -> Prop) : (term37 A B s f) = (term38 A B f s).
Proof. exact (EQ_MP (@lem3477815 A B f s) (@lem3480357 A B f s)). Qed.
Lemma lem3480363 {A B : Type'} (f : type1374 A B) : term681 A B f.
Proof. exact (fun s : A -> Prop => @lem3480358 A B f s). Qed.
Lemma lem3480368 {A B : Type'} : term682 A B.
Proof. exact (fun f : type1374 A B => @lem3480363 A B f). Qed.
