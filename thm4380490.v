Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm4380490_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1822_spec.
Require Import thm18392_spec.
Require Import thm1842_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19490_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211668_spec.
Require Import thm3211669_spec.
Require Import thm3211724_spec.
Require Import thm3211725_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm4372392_spec.
Require Import thm4372393_spec.
Require Import thm4372410_spec.
Require Import thm4374001_spec.
Require Import thm4374285_spec.
Lemma lem4378829 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem4378830 {_105011 : Type'} (s : type686 _105011) (t : type686 _105011) : (s = t) = (term1 _105011 s t).
Proof. exact (@lem4378829 (_105011 -> Prop) s t). Qed.
Lemma lem4378831 {_105011 : Type'} (f : type686 _105011) : (f = (@EMPTY (_105011 -> Prop))) = (term2 _105011 f).
Proof. exact (@lem4378830 _105011 f (@EMPTY (_105011 -> Prop))). Qed.
Lemma lem4378840 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4378841 {_105011 : Type'} (f : type686 _105011) : (term3 _105011 f) = (term4 _105011 f).
Proof. exact (MK_COMB (@lem4378840) (@lem4378831 _105011 f)). Qed.
Lemma lem4378858 {_105011 _105012 : Type'} (t : _105012 -> Prop) : (term5 _105011 _105012 t) = (term5 _105011 _105012 t).
Proof. exact (eq_refl (term5 _105011 _105012 t)). Qed.
Lemma lem4378859 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) : (term6 _105011 _105012 f t) = (term7 _105011 _105012 f t).
Proof. exact (MK_COMB (@lem4378841 _105011 f) (@lem4378858 _105011 _105012 t)). Qed.
Lemma lem4378862 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) : (term7 _105011 _105012 f t) = (term6 _105011 _105012 f t).
Proof. exact (SYM (@lem4378859 _105011 _105012 f t)). Qed.
Lemma lem4378872 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4378873 {_105011 : Type'} (P : type686 _105011) (x : _105011 -> Prop) : (@IN (_105011 -> Prop) x P) = (P x).
Proof. exact (@lem4378872 (_105011 -> Prop) P x). Qed.
Lemma lem4378874 {_105011 : Type'} (f : type686 _105011) (x : _105011 -> Prop) : (@IN (_105011 -> Prop) x f) = (f x).
Proof. exact (@lem4378873 _105011 f x). Qed.
Lemma lem4378875 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4378876 {_105011 : Type'} (f : type686 _105011) (x : _105011 -> Prop) : (term8 _105011 x f) = (term9 _105011 f x).
Proof. exact (MK_COMB (@lem4378875) (@lem4378874 _105011 f x)). Qed.
Lemma lem4378878 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem4378879 {_105011 : Type'} (x : _105011 -> Prop) : (@IN (_105011 -> Prop) x (@EMPTY (_105011 -> Prop))) = False.
Proof. exact (@lem4378878 (_105011 -> Prop) x). Qed.
Lemma lem4378880 {_105011 : Type'} (f : type686 _105011) (x : _105011 -> Prop) : ((@IN (_105011 -> Prop) x f) = (@IN (_105011 -> Prop) x (@EMPTY (_105011 -> Prop)))) = ((f x) = False).
Proof. exact (MK_COMB (@lem4378876 _105011 f x) (@lem4378879 _105011 x)). Qed.
Lemma lem4378882 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem4378883 {_105011 : Type'} (f : type686 _105011) (x : _105011 -> Prop) : ((f x) = False) = (term10 _105011 f x).
Proof. exact (@lem4378882 (f x)). Qed.
Lemma lem4378884 {_105011 : Type'} (f : type686 _105011) (x : _105011 -> Prop) : ((@IN (_105011 -> Prop) x f) = (@IN (_105011 -> Prop) x (@EMPTY (_105011 -> Prop)))) = (term10 _105011 f x).
Proof. exact (TRANS (@lem4378880 _105011 f x) (@lem4378883 _105011 f x)). Qed.
Lemma lem4378885 {_105011 : Type'} (f : type686 _105011) : (term11 _105011 f) = (term12 _105011 f).
Proof. exact (fun_ext (fun x : _105011 -> Prop => @lem4378884 _105011 f x)). Qed.
Lemma lem4378886 {_105011 : Type'} : (@all (_105011 -> Prop)) = (@all (_105011 -> Prop)).
Proof. exact (eq_refl (@all (_105011 -> Prop))). Qed.
Lemma lem4378887 {_105011 : Type'} (f : type686 _105011) : (term2 _105011 f) = (term13 _105011 f).
Proof. exact (MK_COMB (@lem4378886 _105011) (@lem4378885 _105011 f)). Qed.
Lemma lem4378892 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4378893 {_105011 : Type'} (f : type686 _105011) : (term4 _105011 f) = (term14 _105011 f).
Proof. exact (MK_COMB (@lem4378892) (@lem4378887 _105011 f)). Qed.
Lemma lem4378907 {A : Type'} (s : type686 A) (x : A) : (term15 A x s) = (term16 A s x).
Proof. exact (EQ_MP (@lem3211669 A s x) (@lem3211668 A s x)). Qed.
Lemma lem4378908 {_105011 : Type'} (s : type686 _105011) (x : _105011) : (term15 _105011 x s) = (term16 _105011 s x).
Proof. exact (@lem4378907 _105011 s x). Qed.
Lemma lem4378909 {_105011 : Type'} (p1 : _105011) : (term17 _105011 p1) = (term18 _105011 p1).
Proof. exact (@lem4378908 _105011 (@EMPTY (_105011 -> Prop)) p1). Qed.
Lemma lem4378917 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem4378918 {_105011 : Type'} (x : _105011 -> Prop) : (@IN (_105011 -> Prop) x (@EMPTY (_105011 -> Prop))) = False.
Proof. exact (@lem4378917 (_105011 -> Prop) x). Qed.
Lemma lem4378919 {_105011 : Type'} (t : _105011 -> Prop) : (@IN (_105011 -> Prop) t (@EMPTY (_105011 -> Prop))) = False.
Proof. exact (@lem4378918 _105011 t). Qed.
Lemma lem4378920 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4378921 {_105011 : Type'} (t : _105011 -> Prop) : (term19 _105011 t) = (imp False).
Proof. exact (MK_COMB (@lem4378920) (@lem4378919 _105011 t)). Qed.
Lemma lem4378923 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4378924 {_105011 : Type'} (P : _105011 -> Prop) (x : _105011) : (@IN _105011 x P) = (P x).
Proof. exact (@lem4378923 _105011 P x). Qed.
Lemma lem4378925 {_105011 : Type'} (t : _105011 -> Prop) (p1 : _105011) : (@IN _105011 p1 t) = (t p1).
Proof. exact (@lem4378924 _105011 t p1). Qed.
Lemma lem4378926 {_105011 : Type'} (t : _105011 -> Prop) (p1 : _105011) : (term20 _105011 p1 t) = (term21 _105011 t p1).
Proof. exact (MK_COMB (@lem4378921 _105011 t) (@lem4378925 _105011 t p1)). Qed.
Lemma lem4378928 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem4378929 {_105011 : Type'} (t : _105011 -> Prop) (p1 : _105011) : (term21 _105011 t p1) = True.
Proof. exact (@lem4378928 (t p1)). Qed.
Lemma lem4378930 {_105011 : Type'} (p1 : _105011) (t : _105011 -> Prop) : (term20 _105011 p1 t) = True.
Proof. exact (TRANS (@lem4378926 _105011 t p1) (@lem4378929 _105011 t p1)). Qed.
Lemma lem4378931 {_105011 : Type'} (p1 : _105011) : (term22 _105011 p1) = (term23 _105011).
Proof. exact (fun_ext (fun t : _105011 -> Prop => @lem4378930 _105011 p1 t)). Qed.
Lemma lem4378932 {_105011 : Type'} : (@all (_105011 -> Prop)) = (@all (_105011 -> Prop)).
Proof. exact (eq_refl (@all (_105011 -> Prop))). Qed.
Lemma lem4378933 {_105011 : Type'} (p1 : _105011) : (term18 _105011 p1) = (term24 _105011).
Proof. exact (MK_COMB (@lem4378932 _105011) (@lem4378931 _105011 p1)). Qed.
Lemma lem4378935 {A : Type'} (t : Prop) : (term25 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4378936 {_105011 : Type'} (t : Prop) : (term26 _105011 t) = t.
Proof. exact (@lem4378935 (_105011 -> Prop) t). Qed.
Lemma lem4378937 {_105011 : Type'} : (term24 _105011) = True.
Proof. exact (@lem4378936 _105011 True). Qed.
Lemma lem4378938 {_105011 : Type'} (p1 : _105011) : (term18 _105011 p1) = True.
Proof. exact (TRANS (@lem4378933 _105011 p1) (@lem4378937 _105011)). Qed.
Lemma lem4378939 {_105011 : Type'} (p1 : _105011) : (term17 _105011 p1) = True.
Proof. exact (TRANS (@lem4378909 _105011 p1) (@lem4378938 _105011 p1)). Qed.
Lemma lem4378940 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4378941 {_105011 : Type'} (p1 : _105011) : (term27 _105011 p1) = (and True).
Proof. exact (MK_COMB (@lem4378940) (@lem4378939 _105011 p1)). Qed.
Lemma lem4378943 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4378944 {_105012 : Type'} (P : _105012 -> Prop) (x : _105012) : (@IN _105012 x P) = (P x).
Proof. exact (@lem4378943 _105012 P x). Qed.
Lemma lem4378945 {_105012 : Type'} (t : _105012 -> Prop) (p2 : _105012) : (@IN _105012 p2 t) = (t p2).
Proof. exact (@lem4378944 _105012 t p2). Qed.
Lemma lem4378946 {_105011 _105012 : Type'} (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term28 _105011 _105012 p1 p2 t) = (term29 _105012 t p2).
Proof. exact (MK_COMB (@lem4378941 _105011 p1) (@lem4378945 _105012 t p2)). Qed.
Lemma lem4378948 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4378949 {_105012 : Type'} (t : _105012 -> Prop) (p2 : _105012) : (term29 _105012 t p2) = (t p2).
Proof. exact (@lem4378948 (t p2)). Qed.
Lemma lem4378950 {_105011 _105012 : Type'} (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term28 _105011 _105012 p1 p2 t) = (t p2).
Proof. exact (TRANS (@lem4378946 _105011 _105012 p1 t p2) (@lem4378949 _105012 t p2)). Qed.
Lemma lem4378951 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4378952 {_105011 _105012 : Type'} (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term30 _105011 _105012 p1 p2 t) = (term31 _105012 t p2).
Proof. exact (MK_COMB (@lem4378951) (@lem4378950 _105011 _105012 p1 t p2)). Qed.
Lemma lem4378956 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem3211725 A x) (@lem3211724 A x)). Qed.
Lemma lem4378957 {_105011 : Type'} (x : _105011) : (@IN _105011 x (@UNIV _105011)) = True.
Proof. exact (@lem4378956 _105011 x). Qed.
Lemma lem4378958 {_105011 : Type'} (p1 : _105011) : (@IN _105011 p1 (@UNIV _105011)) = True.
Proof. exact (@lem4378957 _105011 p1). Qed.
Lemma lem4378959 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4378960 {_105011 : Type'} (p1 : _105011) : (term32 _105011 p1) = (and True).
Proof. exact (MK_COMB (@lem4378959) (@lem4378958 _105011 p1)). Qed.
Lemma lem4378962 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4378963 {_105012 : Type'} (P : _105012 -> Prop) (x : _105012) : (@IN _105012 x P) = (P x).
Proof. exact (@lem4378962 _105012 P x). Qed.
Lemma lem4378964 {_105012 : Type'} (t : _105012 -> Prop) (p2 : _105012) : (@IN _105012 p2 t) = (t p2).
Proof. exact (@lem4378963 _105012 t p2). Qed.
Lemma lem4378965 {_105011 _105012 : Type'} (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term33 _105011 _105012 p1 p2 t) = (term29 _105012 t p2).
Proof. exact (MK_COMB (@lem4378960 _105011 p1) (@lem4378964 _105012 t p2)). Qed.
Lemma lem4378967 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4378968 {_105012 : Type'} (t : _105012 -> Prop) (p2 : _105012) : (term29 _105012 t p2) = (t p2).
Proof. exact (@lem4378967 (t p2)). Qed.
Lemma lem4378969 {_105011 _105012 : Type'} (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term33 _105011 _105012 p1 p2 t) = (t p2).
Proof. exact (TRANS (@lem4378965 _105011 _105012 p1 t p2) (@lem4378968 _105012 t p2)). Qed.
Lemma lem4378970 {_105011 _105012 : Type'} (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : ((term28 _105011 _105012 p1 p2 t) = (term33 _105011 _105012 p1 p2 t)) = ((t p2) = (t p2)).
Proof. exact (MK_COMB (@lem4378952 _105011 _105012 p1 t p2) (@lem4378969 _105011 _105012 p1 t p2)). Qed.
Lemma lem4378972 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4378973 (x : Prop) : (x = x) = True.
Proof. exact (@lem4378972 Prop x). Qed.
Lemma lem4378974 {_105012 : Type'} (t : _105012 -> Prop) (p2 : _105012) : ((t p2) = (t p2)) = True.
Proof. exact (@lem4378973 (t p2)). Qed.
Lemma lem4378975 {_105011 _105012 : Type'} (p1 : _105011) (p2 : _105012) (t : _105012 -> Prop) : ((term28 _105011 _105012 p1 p2 t) = (term33 _105011 _105012 p1 p2 t)) = True.
Proof. exact (TRANS (@lem4378970 _105011 _105012 p1 t p2) (@lem4378974 _105012 t p2)). Qed.
Lemma lem4378976 {_105011 _105012 : Type'} (p1 : _105011) (t : _105012 -> Prop) : (term34 _105011 _105012 p1 t) = (term35 _105012).
Proof. exact (fun_ext (fun p2 : _105012 => @lem4378975 _105011 _105012 p1 p2 t)). Qed.
Lemma lem4378977 {_105012 : Type'} : (@all _105012) = (@all _105012).
Proof. exact (eq_refl (@all _105012)). Qed.
Lemma lem4378978 {_105011 _105012 : Type'} (p1 : _105011) (t : _105012 -> Prop) : (term36 _105011 _105012 p1 t) = (term37 _105012).
Proof. exact (MK_COMB (@lem4378977 _105012) (@lem4378976 _105011 _105012 p1 t)). Qed.
Lemma lem4378980 {A : Type'} (t : Prop) : (term25 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4378981 {_105012 : Type'} (t : Prop) : (term25 _105012 t) = t.
Proof. exact (@lem4378980 _105012 t). Qed.
Lemma lem4378982 {_105012 : Type'} : (term37 _105012) = True.
Proof. exact (@lem4378981 _105012 True). Qed.
Lemma lem4378983 {_105011 _105012 : Type'} (p1 : _105011) (t : _105012 -> Prop) : (term36 _105011 _105012 p1 t) = True.
Proof. exact (TRANS (@lem4378978 _105011 _105012 p1 t) (@lem4378982 _105012)). Qed.
Lemma lem4378984 {_105011 _105012 : Type'} (t : _105012 -> Prop) : (term38 _105011 _105012 t) = (term35 _105011).
Proof. exact (fun_ext (fun p1 : _105011 => @lem4378983 _105011 _105012 p1 t)). Qed.
Lemma lem4378985 {_105011 : Type'} : (@all _105011) = (@all _105011).
Proof. exact (eq_refl (@all _105011)). Qed.
Lemma lem4378986 {_105011 _105012 : Type'} (t : _105012 -> Prop) : (term5 _105011 _105012 t) = (term37 _105011).
Proof. exact (MK_COMB (@lem4378985 _105011) (@lem4378984 _105011 _105012 t)). Qed.
Lemma lem4378988 {A : Type'} (t : Prop) : (term25 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4378989 {_105011 : Type'} (t : Prop) : (term25 _105011 t) = t.
Proof. exact (@lem4378988 _105011 t). Qed.
Lemma lem4378990 {_105011 : Type'} : (term37 _105011) = True.
Proof. exact (@lem4378989 _105011 True). Qed.
Lemma lem4378991 {_105011 _105012 : Type'} (t : _105012 -> Prop) : (term5 _105011 _105012 t) = True.
Proof. exact (TRANS (@lem4378986 _105011 _105012 t) (@lem4378990 _105011)). Qed.
Lemma lem4378992 {_105011 _105012 : Type'} (t : _105012 -> Prop) (f : type686 _105011) : (term7 _105011 _105012 f t) = (term39 _105011 f).
Proof. exact (MK_COMB (@lem4378893 _105011 f) (@lem4378991 _105011 _105012 t)). Qed.
Lemma lem4378994 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem4378995 {_105011 : Type'} (f : type686 _105011) : (term39 _105011 f) = True.
Proof. exact (@lem4378994 (term13 _105011 f)). Qed.
Lemma lem4378996 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) : (term7 _105011 _105012 f t) = True.
Proof. exact (TRANS (@lem4378992 _105011 _105012 t f) (@lem4378995 _105011 f)). Qed.
Lemma lem4378997 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) : True = (term7 _105011 _105012 f t).
Proof. exact (SYM (@lem4378996 _105011 _105012 f t)). Qed.
Lemma lem4378998 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) : term7 _105011 _105012 f t.
Proof. exact (EQ_MP (@lem4378997 _105011 _105012 f t) (@lem0)). Qed.
Lemma lem4378999 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) : term6 _105011 _105012 f t.
Proof. exact (EQ_MP (@lem4378862 _105011 _105012 f t) (@lem4378998 _105011 _105012 f t)). Qed.
Lemma lem4379000 {_105011 _105012 : Type'} (t : _105012 -> Prop) (f : type686 _105011) (h1 : f = (@EMPTY (_105011 -> Prop))) : term5 _105011 _105012 t.
Proof. exact (@lem4378999 _105011 _105012 f t (@lem4372393 _105011 f h1)). Qed.
Lemma lem4379016 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem4379017 {_105011 : Type'} (s : type686 _105011) (t : type686 _105011) : (s = t) = (term1 _105011 s t).
Proof. exact (@lem4379016 (_105011 -> Prop) s t). Qed.
Lemma lem4379018 {_105011 : Type'} (f : type686 _105011) : (f = (@EMPTY (_105011 -> Prop))) = (term2 _105011 f).
Proof. exact (@lem4379017 _105011 f (@EMPTY (_105011 -> Prop))). Qed.
Lemma lem4379027 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4379028 {_105011 : Type'} (f : type686 _105011) : (term40 _105011 f) = (term41 _105011 f).
Proof. exact (MK_COMB (@lem4379027) (@lem4379018 _105011 f)). Qed.
Lemma lem4379029 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4379030 {_105011 : Type'} (f : type686 _105011) : (term42 _105011 f) = (term43 _105011 f).
Proof. exact (MK_COMB (@lem4379029) (@lem4379028 _105011 f)). Qed.
Lemma lem4379053 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) : (term44 _105011 _105012 f t) = (term44 _105011 _105012 f t).
Proof. exact (eq_refl (term44 _105011 _105012 f t)). Qed.
Lemma lem4379054 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) : (term45 _105011 _105012 f t) = (term46 _105011 _105012 f t).
Proof. exact (MK_COMB (@lem4379030 _105011 f) (@lem4379053 _105011 _105012 f t)). Qed.
Lemma lem4379057 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) : (term46 _105011 _105012 f t) = (term45 _105011 _105012 f t).
Proof. exact (SYM (@lem4379054 _105011 _105012 f t)). Qed.
Lemma lem4379067 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4379068 {_105011 : Type'} (P : type686 _105011) (x : _105011 -> Prop) : (@IN (_105011 -> Prop) x P) = (P x).
Proof. exact (@lem4379067 (_105011 -> Prop) P x). Qed.
Lemma lem4379069 {_105011 : Type'} (f : type686 _105011) (x : _105011 -> Prop) : (@IN (_105011 -> Prop) x f) = (f x).
Proof. exact (@lem4379068 _105011 f x). Qed.
Lemma lem4379070 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4379071 {_105011 : Type'} (f : type686 _105011) (x : _105011 -> Prop) : (term8 _105011 x f) = (term9 _105011 f x).
Proof. exact (MK_COMB (@lem4379070) (@lem4379069 _105011 f x)). Qed.
Lemma lem4379073 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem4379074 {_105011 : Type'} (x : _105011 -> Prop) : (@IN (_105011 -> Prop) x (@EMPTY (_105011 -> Prop))) = False.
Proof. exact (@lem4379073 (_105011 -> Prop) x). Qed.
Lemma lem4379075 {_105011 : Type'} (f : type686 _105011) (x : _105011 -> Prop) : ((@IN (_105011 -> Prop) x f) = (@IN (_105011 -> Prop) x (@EMPTY (_105011 -> Prop)))) = ((f x) = False).
Proof. exact (MK_COMB (@lem4379071 _105011 f x) (@lem4379074 _105011 x)). Qed.
Lemma lem4379077 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem4379078 {_105011 : Type'} (f : type686 _105011) (x : _105011 -> Prop) : ((f x) = False) = (term10 _105011 f x).
Proof. exact (@lem4379077 (f x)). Qed.
Lemma lem4379079 {_105011 : Type'} (f : type686 _105011) (x : _105011 -> Prop) : ((@IN (_105011 -> Prop) x f) = (@IN (_105011 -> Prop) x (@EMPTY (_105011 -> Prop)))) = (term10 _105011 f x).
Proof. exact (TRANS (@lem4379075 _105011 f x) (@lem4379078 _105011 f x)). Qed.
Lemma lem4379080 {_105011 : Type'} (f : type686 _105011) : (term11 _105011 f) = (term12 _105011 f).
Proof. exact (fun_ext (fun x : _105011 -> Prop => @lem4379079 _105011 f x)). Qed.
Lemma lem4379081 {_105011 : Type'} : (@all (_105011 -> Prop)) = (@all (_105011 -> Prop)).
Proof. exact (eq_refl (@all (_105011 -> Prop))). Qed.
Lemma lem4379082 {_105011 : Type'} (f : type686 _105011) : (term2 _105011 f) = (term13 _105011 f).
Proof. exact (MK_COMB (@lem4379081 _105011) (@lem4379080 _105011 f)). Qed.
Lemma lem4379087 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4379088 {_105011 : Type'} (f : type686 _105011) : (term41 _105011 f) = (term47 _105011 f).
Proof. exact (MK_COMB (@lem4379087) (@lem4379082 _105011 f)). Qed.
Lemma lem4379089 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4379090 {_105011 : Type'} (f : type686 _105011) : (term43 _105011 f) = (term48 _105011 f).
Proof. exact (MK_COMB (@lem4379089) (@lem4379088 _105011 f)). Qed.
Lemma lem4379104 {A : Type'} (s : type686 A) (x : A) : (term15 A x s) = (term16 A s x).
Proof. exact (EQ_MP (@lem3211669 A s x) (@lem3211668 A s x)). Qed.
Lemma lem4379105 {_105011 : Type'} (s : type686 _105011) (x : _105011) : (term15 _105011 x s) = (term16 _105011 s x).
Proof. exact (@lem4379104 _105011 s x). Qed.
Lemma lem4379106 {_105011 : Type'} (f : type686 _105011) (p1 : _105011) : (term15 _105011 p1 f) = (term16 _105011 f p1).
Proof. exact (@lem4379105 _105011 f p1). Qed.
Lemma lem4379114 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4379115 {_105011 : Type'} (P : type686 _105011) (x : _105011 -> Prop) : (@IN (_105011 -> Prop) x P) = (P x).
Proof. exact (@lem4379114 (_105011 -> Prop) P x). Qed.
Lemma lem4379116 {_105011 : Type'} (f : type686 _105011) (t : _105011 -> Prop) : (@IN (_105011 -> Prop) t f) = (f t).
Proof. exact (@lem4379115 _105011 f t). Qed.
Lemma lem4379117 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4379118 {_105011 : Type'} (f : type686 _105011) (t : _105011 -> Prop) : (term49 _105011 t f) = (term50 _105011 f t).
Proof. exact (MK_COMB (@lem4379117) (@lem4379116 _105011 f t)). Qed.
Lemma lem4379120 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4379121 {_105011 : Type'} (P : _105011 -> Prop) (x : _105011) : (@IN _105011 x P) = (P x).
Proof. exact (@lem4379120 _105011 P x). Qed.
Lemma lem4379122 {_105011 : Type'} (t : _105011 -> Prop) (p1 : _105011) : (@IN _105011 p1 t) = (t p1).
Proof. exact (@lem4379121 _105011 t p1). Qed.
Lemma lem4379123 {_105011 : Type'} (f : type686 _105011) (t : _105011 -> Prop) (p1 : _105011) : (term51 _105011 f p1 t) = (term52 _105011 f t p1).
Proof. exact (MK_COMB (@lem4379118 _105011 f t) (@lem4379122 _105011 t p1)). Qed.
Lemma lem4379126 {_105011 : Type'} (f : type686 _105011) (p1 : _105011) : (term53 _105011 f p1) = (term54 _105011 f p1).
Proof. exact (fun_ext (fun t : _105011 -> Prop => @lem4379123 _105011 f t p1)). Qed.
Lemma lem4379127 {_105011 : Type'} : (@all (_105011 -> Prop)) = (@all (_105011 -> Prop)).
Proof. exact (eq_refl (@all (_105011 -> Prop))). Qed.
Lemma lem4379128 {_105011 : Type'} (f : type686 _105011) (p1 : _105011) : (term16 _105011 f p1) = (term55 _105011 f p1).
Proof. exact (MK_COMB (@lem4379127 _105011) (@lem4379126 _105011 f p1)). Qed.
Lemma lem4379133 {_105011 : Type'} (f : type686 _105011) (p1 : _105011) : (term15 _105011 p1 f) = (term55 _105011 f p1).
Proof. exact (TRANS (@lem4379106 _105011 f p1) (@lem4379128 _105011 f p1)). Qed.
Lemma lem4379134 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4379135 {_105011 : Type'} (f : type686 _105011) (p1 : _105011) : (term56 _105011 p1 f) = (term57 _105011 f p1).
Proof. exact (MK_COMB (@lem4379134) (@lem4379133 _105011 f p1)). Qed.
Lemma lem4379137 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4379138 {_105012 : Type'} (P : _105012 -> Prop) (x : _105012) : (@IN _105012 x P) = (P x).
Proof. exact (@lem4379137 _105012 P x). Qed.
Lemma lem4379139 {_105012 : Type'} (t : _105012 -> Prop) (p2 : _105012) : (@IN _105012 p2 t) = (t p2).
Proof. exact (@lem4379138 _105012 t p2). Qed.
Lemma lem4379140 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term58 _105011 _105012 p1 f p2 t) = (term59 _105011 _105012 f p1 t p2).
Proof. exact (MK_COMB (@lem4379135 _105011 f p1) (@lem4379139 _105012 t p2)). Qed.
Lemma lem4379143 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4379144 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term60 _105011 _105012 p1 f p2 t) = (term61 _105011 _105012 f p1 t p2).
Proof. exact (MK_COMB (@lem4379143) (@lem4379140 _105011 _105012 f p1 t p2)). Qed.
Lemma lem4379152 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4379153 {_105011 : Type'} (P : type686 _105011) (x : _105011 -> Prop) : (@IN (_105011 -> Prop) x P) = (P x).
Proof. exact (@lem4379152 (_105011 -> Prop) P x). Qed.
Lemma lem4379154 {_105011 : Type'} (f : type686 _105011) (s : _105011 -> Prop) : (@IN (_105011 -> Prop) s f) = (f s).
Proof. exact (@lem4379153 _105011 f s). Qed.
Lemma lem4379155 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4379156 {_105011 : Type'} (f : type686 _105011) (s : _105011 -> Prop) : (term49 _105011 s f) = (term50 _105011 f s).
Proof. exact (MK_COMB (@lem4379155) (@lem4379154 _105011 f s)). Qed.
Lemma lem4379160 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4379161 {_105011 : Type'} (P : _105011 -> Prop) (x : _105011) : (@IN _105011 x P) = (P x).
Proof. exact (@lem4379160 _105011 P x). Qed.
Lemma lem4379162 {_105011 : Type'} (s : _105011 -> Prop) (p1 : _105011) : (@IN _105011 p1 s) = (s p1).
Proof. exact (@lem4379161 _105011 s p1). Qed.
Lemma lem4379163 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4379164 {_105011 : Type'} (s : _105011 -> Prop) (p1 : _105011) : (term62 _105011 p1 s) = (term63 _105011 s p1).
Proof. exact (MK_COMB (@lem4379163) (@lem4379162 _105011 s p1)). Qed.
Lemma lem4379166 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4379167 {_105012 : Type'} (P : _105012 -> Prop) (x : _105012) : (@IN _105012 x P) = (P x).
Proof. exact (@lem4379166 _105012 P x). Qed.
Lemma lem4379168 {_105012 : Type'} (t : _105012 -> Prop) (p2 : _105012) : (@IN _105012 p2 t) = (t p2).
Proof. exact (@lem4379167 _105012 t p2). Qed.
Lemma lem4379169 {_105011 _105012 : Type'} (s : _105011 -> Prop) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term64 _105011 _105012 p1 s p2 t) = (term65 _105011 _105012 s p1 t p2).
Proof. exact (MK_COMB (@lem4379164 _105011 s p1) (@lem4379168 _105012 t p2)). Qed.
Lemma lem4379172 {_105011 _105012 : Type'} (f : type686 _105011) (s : _105011 -> Prop) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term66 _105011 _105012 f p1 s p2 t) = (term67 _105011 _105012 f s p1 t p2).
Proof. exact (MK_COMB (@lem4379156 _105011 f s) (@lem4379169 _105011 _105012 s p1 t p2)). Qed.
Lemma lem4379175 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term68 _105011 _105012 f p1 p2 t) = (term69 _105011 _105012 f p1 t p2).
Proof. exact (fun_ext (fun s : _105011 -> Prop => @lem4379172 _105011 _105012 f s p1 t p2)). Qed.
Lemma lem4379176 {_105011 : Type'} : (@all (_105011 -> Prop)) = (@all (_105011 -> Prop)).
Proof. exact (eq_refl (@all (_105011 -> Prop))). Qed.
Lemma lem4379177 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term70 _105011 _105012 f p1 p2 t) = (term71 _105011 _105012 f p1 t p2).
Proof. exact (MK_COMB (@lem4379176 _105011) (@lem4379175 _105011 _105012 f p1 t p2)). Qed.
Lemma lem4379182 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : ((term58 _105011 _105012 p1 f p2 t) = (term70 _105011 _105012 f p1 p2 t)) = ((term59 _105011 _105012 f p1 t p2) = (term71 _105011 _105012 f p1 t p2)).
Proof. exact (MK_COMB (@lem4379144 _105011 _105012 f p1 t p2) (@lem4379177 _105011 _105012 f p1 t p2)). Qed.
Lemma lem4379185 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) : (term72 _105011 _105012 f p1 t) = (term73 _105011 _105012 f p1 t).
Proof. exact (fun_ext (fun p2 : _105012 => @lem4379182 _105011 _105012 f p1 t p2)). Qed.
Lemma lem4379186 {_105012 : Type'} : (@all _105012) = (@all _105012).
Proof. exact (eq_refl (@all _105012)). Qed.
Lemma lem4379187 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) : (term74 _105011 _105012 f p1 t) = (term75 _105011 _105012 f p1 t).
Proof. exact (MK_COMB (@lem4379186 _105012) (@lem4379185 _105011 _105012 f p1 t)). Qed.
Lemma lem4379192 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) : (term76 _105011 _105012 f t) = (term77 _105011 _105012 f t).
Proof. exact (fun_ext (fun p1 : _105011 => @lem4379187 _105011 _105012 f p1 t)). Qed.
Lemma lem4379193 {_105011 : Type'} : (@all _105011) = (@all _105011).
Proof. exact (eq_refl (@all _105011)). Qed.
Lemma lem4379194 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) : (term44 _105011 _105012 f t) = (term78 _105011 _105012 f t).
Proof. exact (MK_COMB (@lem4379193 _105011) (@lem4379192 _105011 _105012 f t)). Qed.
Lemma lem4379199 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) : (term46 _105011 _105012 f t) = (term79 _105011 _105012 f t).
Proof. exact (MK_COMB (@lem4379090 _105011 f) (@lem4379194 _105011 _105012 f t)). Qed.
Lemma lem4379202 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) : (term79 _105011 _105012 f t) = (term46 _105011 _105012 f t).
Proof. exact (SYM (@lem4379199 _105011 _105012 f t)). Qed.
Lemma lem4379204 (p : Prop) : p = (term80 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4379205 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) : (term79 _105011 _105012 f t) = (term81 _105011 _105012 f t).
Proof. exact (@lem4379204 (term79 _105011 _105012 f t)). Qed.
Lemma lem4379206 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) : (term81 _105011 _105012 f t) = (term79 _105011 _105012 f t).
Proof. exact (SYM (@lem4379205 _105011 _105012 f t)). Qed.
Lemma lem4379207 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) (h1 : term82 _105011 _105012 f t) : term82 _105011 _105012 f t.
Proof. exact (h1). Qed.
Lemma lem4379210 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) (h1 : term81 _105011 _105012 f t) : term81 _105011 _105012 f t.
Proof. exact (h1). Qed.
Lemma lem4379211 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) : term83 _105011 _105012 f t.
Proof. exact (fun h0 : term81 _105011 _105012 f t => @lem4379210 _105011 _105012 f t h0). Qed.
Lemma lem4379212 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) (h1 : term83 _105011 _105012 f t) : term83 _105011 _105012 f t.
Proof. exact (h1). Qed.
Lemma lem4379213 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) (h1 : term81 _105011 _105012 f t) : term81 _105011 _105012 f t.
Proof. exact (h1). Qed.
Lemma lem4379214 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) (h1 : term81 _105011 _105012 f t) (h2 : term83 _105011 _105012 f t) : term81 _105011 _105012 f t.
Proof. exact (@lem4379212 _105011 _105012 f t h2 (@lem4379213 _105011 _105012 f t h1)). Qed.
Lemma lem4379215 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) (h1 : term81 _105011 _105012 f t) : term84 _105011 _105012 f t.
Proof. exact (fun h0 : term83 _105011 _105012 f t => @lem4379214 _105011 _105012 f t h1 h0). Qed.
Lemma lem4379216 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) (h1 : term83 _105011 _105012 f t) : term83 _105011 _105012 f t.
Proof. exact (h1). Qed.
Lemma lem4379217 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) (h1 : term81 _105011 _105012 f t) (h2 : term83 _105011 _105012 f t) : term81 _105011 _105012 f t.
Proof. exact (@lem4379215 _105011 _105012 f t h1 (@lem4379216 _105011 _105012 f t h2)). Qed.
Lemma lem4379218 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) (h1 : term83 _105011 _105012 f t) : term83 _105011 _105012 f t.
Proof. exact (fun h0 : term81 _105011 _105012 f t => @lem4379217 _105011 _105012 f t h0 h1). Qed.
Lemma lem4379219 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) : term85 _105011 _105012 f t.
Proof. exact (fun h0 : term83 _105011 _105012 f t => @lem4379218 _105011 _105012 f t h0). Qed.
Lemma lem4379222 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) : term83 _105011 _105012 f t.
Proof. exact (@lem4379219 _105011 _105012 f t (@lem4379211 _105011 _105012 f t)). Qed.
Lemma lem4379223 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) : term83 _105011 _105012 f t.
Proof. exact (@lem4379222 _105011 _105012 f t). Qed.
Lemma lem4379233 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4379234 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) : (term81 _105011 _105012 f t) = (term86 _105011 _105012 f t).
Proof. exact (@lem4379233 (term82 _105011 _105012 f t)). Qed.
Lemma lem4379236 (t : Prop) : (term87 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4379237 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) : (term86 _105011 _105012 f t) = (term79 _105011 _105012 f t).
Proof. exact (@lem4379236 (term79 _105011 _105012 f t)). Qed.
Lemma lem4379240 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) : (term81 _105011 _105012 f t) = (term79 _105011 _105012 f t).
Proof. exact (TRANS (@lem4379234 _105011 _105012 f t) (@lem4379237 _105011 _105012 f t)). Qed.
Lemma lem4379269 {_105011 _105012 : Type'} (t : _105012 -> Prop) : (term88 _105011 _105012 t) = (term89 _105011 _105012 t).
Proof. exact (fun_ext (fun f : type686 _105011 => @lem4379240 _105011 _105012 f t)). Qed.
Lemma lem4379270 {_105011 : Type'} : (@all ((_105011 -> Prop) -> Prop)) = (@all ((_105011 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_105011 -> Prop) -> Prop))). Qed.
Lemma lem4379271 {_105011 _105012 : Type'} (t : _105012 -> Prop) : (term90 _105011 _105012 t) = (term91 _105011 _105012 t).
Proof. exact (MK_COMB (@lem4379270 _105011) (@lem4379269 _105011 _105012 t)). Qed.
Lemma lem4379276 {_105011 _105012 : Type'} : (term92 _105011 _105012) = (term93 _105011 _105012).
Proof. exact (fun_ext (fun t : _105012 -> Prop => @lem4379271 _105011 _105012 t)). Qed.
Lemma lem4379277 {_105012 : Type'} : (@all (_105012 -> Prop)) = (@all (_105012 -> Prop)).
Proof. exact (eq_refl (@all (_105012 -> Prop))). Qed.
Lemma lem4379286 {_105011 _105012 : Type'} : (term94 _105011 _105012) = (term95 _105011 _105012).
Proof. exact (MK_COMB (@lem4379277 _105012) (@lem4379276 _105011 _105012)). Qed.
Lemma lem4379295 {_105011 _105012 : Type'} (f : type686 _105011) (s : _105011 -> Prop) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term67 _105011 _105012 f s p1 t p2) = (term67 _105011 _105012 f s p1 t p2).
Proof. exact (eq_refl (term67 _105011 _105012 f s p1 t p2)). Qed.
Lemma lem4379296 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term69 _105011 _105012 f p1 t p2) = (term69 _105011 _105012 f p1 t p2).
Proof. exact (fun_ext (fun s : _105011 -> Prop => @lem4379295 _105011 _105012 f s p1 t p2)). Qed.
Lemma lem4379297 {_105011 : Type'} : (@all (_105011 -> Prop)) = (@all (_105011 -> Prop)).
Proof. exact (eq_refl (@all (_105011 -> Prop))). Qed.
Lemma lem4379298 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term71 _105011 _105012 f p1 t p2) = (term71 _105011 _105012 f p1 t p2).
Proof. exact (MK_COMB (@lem4379297 _105011) (@lem4379296 _105011 _105012 f p1 t p2)). Qed.
Lemma lem4379299 {_105012 : Type'} (t : _105012 -> Prop) (p2 : _105012) : (t p2) = (t p2).
Proof. exact (eq_refl (t p2)). Qed.
Lemma lem4379304 {_105011 : Type'} (f : type686 _105011) (t : _105011 -> Prop) (p1 : _105011) : (term52 _105011 f t p1) = (term52 _105011 f t p1).
Proof. exact (eq_refl (term52 _105011 f t p1)). Qed.
Lemma lem4379305 {_105011 : Type'} (f : type686 _105011) (p1 : _105011) : (term54 _105011 f p1) = (term54 _105011 f p1).
Proof. exact (fun_ext (fun t : _105011 -> Prop => @lem4379304 _105011 f t p1)). Qed.
Lemma lem4379306 {_105011 : Type'} : (@all (_105011 -> Prop)) = (@all (_105011 -> Prop)).
Proof. exact (eq_refl (@all (_105011 -> Prop))). Qed.
Lemma lem4379307 {_105011 : Type'} (f : type686 _105011) (p1 : _105011) : (term55 _105011 f p1) = (term55 _105011 f p1).
Proof. exact (MK_COMB (@lem4379306 _105011) (@lem4379305 _105011 f p1)). Qed.
Lemma lem4379308 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4379309 {_105011 : Type'} (f : type686 _105011) (p1 : _105011) : (term57 _105011 f p1) = (term57 _105011 f p1).
Proof. exact (MK_COMB (@lem4379308) (@lem4379307 _105011 f p1)). Qed.
Lemma lem4379310 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term59 _105011 _105012 f p1 t p2) = (term59 _105011 _105012 f p1 t p2).
Proof. exact (MK_COMB (@lem4379309 _105011 f p1) (@lem4379299 _105012 t p2)). Qed.
Lemma lem4379311 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4379312 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term61 _105011 _105012 f p1 t p2) = (term61 _105011 _105012 f p1 t p2).
Proof. exact (MK_COMB (@lem4379311) (@lem4379310 _105011 _105012 f p1 t p2)). Qed.
Lemma lem4379313 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : ((term59 _105011 _105012 f p1 t p2) = (term71 _105011 _105012 f p1 t p2)) = ((term59 _105011 _105012 f p1 t p2) = (term71 _105011 _105012 f p1 t p2)).
Proof. exact (MK_COMB (@lem4379312 _105011 _105012 f p1 t p2) (@lem4379298 _105011 _105012 f p1 t p2)). Qed.
Lemma lem4379314 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) : (term73 _105011 _105012 f p1 t) = (term73 _105011 _105012 f p1 t).
Proof. exact (fun_ext (fun p2 : _105012 => @lem4379313 _105011 _105012 f p1 t p2)). Qed.
Lemma lem4379315 {_105012 : Type'} : (@all _105012) = (@all _105012).
Proof. exact (eq_refl (@all _105012)). Qed.
Lemma lem4379316 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) : (term75 _105011 _105012 f p1 t) = (term75 _105011 _105012 f p1 t).
Proof. exact (MK_COMB (@lem4379315 _105012) (@lem4379314 _105011 _105012 f p1 t)). Qed.
Lemma lem4379317 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) : (term77 _105011 _105012 f t) = (term77 _105011 _105012 f t).
Proof. exact (fun_ext (fun p1 : _105011 => @lem4379316 _105011 _105012 f p1 t)). Qed.
Lemma lem4379318 {_105011 : Type'} : (@all _105011) = (@all _105011).
Proof. exact (eq_refl (@all _105011)). Qed.
Lemma lem4379319 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) : (term78 _105011 _105012 f t) = (term78 _105011 _105012 f t).
Proof. exact (MK_COMB (@lem4379318 _105011) (@lem4379317 _105011 _105012 f t)). Qed.
Lemma lem4379322 {_105011 : Type'} (f : type686 _105011) (x : _105011 -> Prop) : (term10 _105011 f x) = (term10 _105011 f x).
Proof. exact (eq_refl (term10 _105011 f x)). Qed.
Lemma lem4379323 {_105011 : Type'} (f : type686 _105011) : (term12 _105011 f) = (term12 _105011 f).
Proof. exact (fun_ext (fun x : _105011 -> Prop => @lem4379322 _105011 f x)). Qed.
Lemma lem4379324 {_105011 : Type'} : (@all (_105011 -> Prop)) = (@all (_105011 -> Prop)).
Proof. exact (eq_refl (@all (_105011 -> Prop))). Qed.
Lemma lem4379325 {_105011 : Type'} (f : type686 _105011) : (term13 _105011 f) = (term13 _105011 f).
Proof. exact (MK_COMB (@lem4379324 _105011) (@lem4379323 _105011 f)). Qed.
Lemma lem4379326 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4379327 {_105011 : Type'} (f : type686 _105011) : (term47 _105011 f) = (term47 _105011 f).
Proof. exact (MK_COMB (@lem4379326) (@lem4379325 _105011 f)). Qed.
Lemma lem4379328 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4379329 {_105011 : Type'} (f : type686 _105011) : (term48 _105011 f) = (term48 _105011 f).
Proof. exact (MK_COMB (@lem4379328) (@lem4379327 _105011 f)). Qed.
Lemma lem4379330 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) : (term79 _105011 _105012 f t) = (term79 _105011 _105012 f t).
Proof. exact (MK_COMB (@lem4379329 _105011 f) (@lem4379319 _105011 _105012 f t)). Qed.
Lemma lem4379331 {_105011 _105012 : Type'} (t : _105012 -> Prop) : (term89 _105011 _105012 t) = (term89 _105011 _105012 t).
Proof. exact (fun_ext (fun f : type686 _105011 => @lem4379330 _105011 _105012 f t)). Qed.
Lemma lem4379332 {_105011 : Type'} : (@all ((_105011 -> Prop) -> Prop)) = (@all ((_105011 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_105011 -> Prop) -> Prop))). Qed.
Lemma lem4379333 {_105011 _105012 : Type'} (t : _105012 -> Prop) : (term91 _105011 _105012 t) = (term91 _105011 _105012 t).
Proof. exact (MK_COMB (@lem4379332 _105011) (@lem4379331 _105011 _105012 t)). Qed.
Lemma lem4379334 {_105011 _105012 : Type'} : (term93 _105011 _105012) = (term93 _105011 _105012).
Proof. exact (fun_ext (fun t : _105012 -> Prop => @lem4379333 _105011 _105012 t)). Qed.
Lemma lem4379335 {_105012 : Type'} : (@all (_105012 -> Prop)) = (@all (_105012 -> Prop)).
Proof. exact (eq_refl (@all (_105012 -> Prop))). Qed.
Lemma lem4379336 {_105011 _105012 : Type'} : (term95 _105011 _105012) = (term95 _105011 _105012).
Proof. exact (MK_COMB (@lem4379335 _105012) (@lem4379334 _105011 _105012)). Qed.
Lemma lem4379391 {_105011 _105012 : Type'} : (term94 _105011 _105012) = (term95 _105011 _105012).
Proof. exact (TRANS (@lem4379286 _105011 _105012) (@lem4379336 _105011 _105012)). Qed.
Lemma lem4379392 {_105011 _105012 : Type'} : (term95 _105011 _105012) = (term94 _105011 _105012).
Proof. exact (SYM (@lem4379391 _105011 _105012)). Qed.
Lemma lem4379393 {_105011 : Type'} (f : type686 _105011) (h1 : term47 _105011 f) : term47 _105011 f.
Proof. exact (h1). Qed.
Lemma lem4379395 (p : Prop) : p = (term80 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4379396 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : ((term59 _105011 _105012 f p1 t p2) = (term71 _105011 _105012 f p1 t p2)) = (term96 _105011 _105012 f p1 t p2).
Proof. exact (@lem4379395 ((term59 _105011 _105012 f p1 t p2) = (term71 _105011 _105012 f p1 t p2))). Qed.
Lemma lem4379397 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term96 _105011 _105012 f p1 t p2) = ((term59 _105011 _105012 f p1 t p2) = (term71 _105011 _105012 f p1 t p2)).
Proof. exact (SYM (@lem4379396 _105011 _105012 f p1 t p2)). Qed.
Lemma lem4379398 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) (h1 : term97 _105011 _105012 f p1 t p2) : term97 _105011 _105012 f p1 t p2.
Proof. exact (h1). Qed.
Lemma lem4379401 {_105011 : Type'} (f : type686 _105011) (x : _105011 -> Prop) : (term98 _105011 f x) = (f x).
Proof. exact (@lem16933 (f x)). Qed.
Lemma lem4379402 {_105011 : Type'} (P : type686 _105011) : (term99 _105011 P) = (term100 _105011 P).
Proof. exact (@lem18392 (_105011 -> Prop) P). Qed.
Lemma lem4379403 {_105011 : Type'} (f : type686 _105011) : (term47 _105011 f) = (term101 _105011 f).
Proof. exact (@lem4379402 _105011 (term12 _105011 f)). Qed.
Lemma lem4379404 {_105011 : Type'} (f : type686 _105011) (x : _105011 -> Prop) : (term102 _105011 f x) = (term10 _105011 f x).
Proof. exact (eq_refl (term102 _105011 f x)). Qed.
Lemma lem4379405 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4379406 {_105011 : Type'} (f : type686 _105011) (x : _105011 -> Prop) : (term103 _105011 f x) = (term98 _105011 f x).
Proof. exact (MK_COMB (@lem4379405) (@lem4379404 _105011 f x)). Qed.
Lemma lem4379407 {_105011 : Type'} (f : type686 _105011) (x : _105011 -> Prop) : (term103 _105011 f x) = (f x).
Proof. exact (TRANS (@lem4379406 _105011 f x) (@lem4379401 _105011 f x)). Qed.
Lemma lem4379408 {_105011 : Type'} (f : type686 _105011) : (term104 _105011 f) = (term105 _105011 f).
Proof. exact (fun_ext (fun x : _105011 -> Prop => @lem4379407 _105011 f x)). Qed.
Lemma lem4379409 {_105011 : Type'} : (@ex (_105011 -> Prop)) = (@ex (_105011 -> Prop)).
Proof. exact (eq_refl (@ex (_105011 -> Prop))). Qed.
Lemma lem4379410 {_105011 : Type'} (f : type686 _105011) : (term101 _105011 f) = (term106 _105011 f).
Proof. exact (MK_COMB (@lem4379409 _105011) (@lem4379408 _105011 f)). Qed.
Lemma lem4379419 {_105011 : Type'} (f : type686 _105011) : (term47 _105011 f) = (term106 _105011 f).
Proof. exact (TRANS (@lem4379403 _105011 f) (@lem4379410 _105011 f)). Qed.
Lemma lem4379420 {_105011 : Type'} (f : type686 _105011) (h1 : term47 _105011 f) : term106 _105011 f.
Proof. exact (EQ_MP (@lem4379419 _105011 f) (@lem4379393 _105011 f h1)). Qed.
Lemma lem4379429 {_105011 : Type'} (f : type686 _105011) (t : _105011 -> Prop) (p1 : _105011) : (term107 _105011 f t p1) = (term108 _105011 f t p1).
Proof. exact (@lem17362 (f t) (t p1)). Qed.
Lemma lem4379434 {_105011 : Type'} (f : type686 _105011) (t : _105011 -> Prop) (p1 : _105011) : (term52 _105011 f t p1) = (term109 _105011 f t p1).
Proof. exact (@lem17265 (f t) (t p1)). Qed.
Lemma lem4379435 {_105011 : Type'} (P : type686 _105011) : (term99 _105011 P) = (term100 _105011 P).
Proof. exact (@lem18392 (_105011 -> Prop) P). Qed.
Lemma lem4379436 {_105011 : Type'} (f : type686 _105011) (p1 : _105011) : (term110 _105011 f p1) = (term111 _105011 f p1).
Proof. exact (@lem4379435 _105011 (term54 _105011 f p1)). Qed.
Lemma lem4379437 {_105011 : Type'} (f : type686 _105011) (t : _105011 -> Prop) (p1 : _105011) : (term112 _105011 f p1 t) = (term52 _105011 f t p1).
Proof. exact (eq_refl (term112 _105011 f p1 t)). Qed.
Lemma lem4379438 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4379439 {_105011 : Type'} (f : type686 _105011) (t : _105011 -> Prop) (p1 : _105011) : (term113 _105011 f p1 t) = (term107 _105011 f t p1).
Proof. exact (MK_COMB (@lem4379438) (@lem4379437 _105011 f t p1)). Qed.
Lemma lem4379440 {_105011 : Type'} (f : type686 _105011) (t : _105011 -> Prop) (p1 : _105011) : (term113 _105011 f p1 t) = (term108 _105011 f t p1).
Proof. exact (TRANS (@lem4379439 _105011 f t p1) (@lem4379429 _105011 f t p1)). Qed.
Lemma lem4379441 {_105011 : Type'} (f : type686 _105011) (p1 : _105011) : (term114 _105011 f p1) = (term115 _105011 f p1).
Proof. exact (fun_ext (fun t : _105011 -> Prop => @lem4379440 _105011 f t p1)). Qed.
Lemma lem4379442 {_105011 : Type'} : (@ex (_105011 -> Prop)) = (@ex (_105011 -> Prop)).
Proof. exact (eq_refl (@ex (_105011 -> Prop))). Qed.
Lemma lem4379443 {_105011 : Type'} (f : type686 _105011) (p1 : _105011) : (term111 _105011 f p1) = (term116 _105011 f p1).
Proof. exact (MK_COMB (@lem4379442 _105011) (@lem4379441 _105011 f p1)). Qed.
Lemma lem4379444 {_105011 : Type'} (f : type686 _105011) (p1 : _105011) : (term110 _105011 f p1) = (term116 _105011 f p1).
Proof. exact (TRANS (@lem4379436 _105011 f p1) (@lem4379443 _105011 f p1)). Qed.
Lemma lem4379445 {_105011 : Type'} (f : type686 _105011) (p1 : _105011) : (term54 _105011 f p1) = (term117 _105011 f p1).
Proof. exact (fun_ext (fun t : _105011 -> Prop => @lem4379434 _105011 f t p1)). Qed.
Lemma lem4379446 {_105011 : Type'} : (@all (_105011 -> Prop)) = (@all (_105011 -> Prop)).
Proof. exact (eq_refl (@all (_105011 -> Prop))). Qed.
Lemma lem4379447 {_105011 : Type'} (f : type686 _105011) (p1 : _105011) : (term55 _105011 f p1) = (term118 _105011 f p1).
Proof. exact (MK_COMB (@lem4379446 _105011) (@lem4379445 _105011 f p1)). Qed.
Lemma lem4379448 {_105012 : Type'} (t : _105012 -> Prop) (p2 : _105012) : (term119 _105012 t p2) = (term119 _105012 t p2).
Proof. exact (eq_refl (term119 _105012 t p2)). Qed.
Lemma lem4379449 {_105012 : Type'} (t : _105012 -> Prop) (p2 : _105012) : (t p2) = (t p2).
Proof. exact (eq_refl (t p2)). Qed.
Lemma lem4379450 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4379451 {_105011 : Type'} (f : type686 _105011) (p1 : _105011) : (term120 _105011 f p1) = (term121 _105011 f p1).
Proof. exact (MK_COMB (@lem4379450) (@lem4379444 _105011 f p1)). Qed.
Lemma lem4379452 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term122 _105011 _105012 f p1 t p2) = (term123 _105011 _105012 f p1 t p2).
Proof. exact (MK_COMB (@lem4379451 _105011 f p1) (@lem4379448 _105012 t p2)). Qed.
Lemma lem4379453 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term124 _105011 _105012 f p1 t p2) = (term122 _105011 _105012 f p1 t p2).
Proof. exact (@lem17045 (term55 _105011 f p1) (t p2)). Qed.
Lemma lem4379454 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term124 _105011 _105012 f p1 t p2) = (term123 _105011 _105012 f p1 t p2).
Proof. exact (TRANS (@lem4379453 _105011 _105012 f p1 t p2) (@lem4379452 _105011 _105012 f p1 t p2)). Qed.
Lemma lem4379455 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4379456 {_105011 : Type'} (f : type686 _105011) (p1 : _105011) : (term57 _105011 f p1) = (term125 _105011 f p1).
Proof. exact (MK_COMB (@lem4379455) (@lem4379447 _105011 f p1)). Qed.
Lemma lem4379457 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term59 _105011 _105012 f p1 t p2) = (term126 _105011 _105012 f p1 t p2).
Proof. exact (MK_COMB (@lem4379456 _105011 f p1) (@lem4379449 _105012 t p2)). Qed.
Lemma lem4379468 {_105011 _105012 : Type'} (s : _105011 -> Prop) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term127 _105011 _105012 s p1 t p2) = (term128 _105011 _105012 s p1 t p2).
Proof. exact (@lem17045 (s p1) (t p2)). Qed.
Lemma lem4379473 {_105011 : Type'} (f : type686 _105011) (s : _105011 -> Prop) : (term129 _105011 f s) = (term129 _105011 f s).
Proof. exact (eq_refl (term129 _105011 f s)). Qed.
Lemma lem4379474 {_105011 _105012 : Type'} (f : type686 _105011) (s : _105011 -> Prop) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term130 _105011 _105012 f s p1 t p2) = (term131 _105011 _105012 f s p1 t p2).
Proof. exact (MK_COMB (@lem4379473 _105011 f s) (@lem4379468 _105011 _105012 s p1 t p2)). Qed.
Lemma lem4379475 {_105011 _105012 : Type'} (f : type686 _105011) (s : _105011 -> Prop) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term132 _105011 _105012 f s p1 t p2) = (term130 _105011 _105012 f s p1 t p2).
Proof. exact (@lem17362 (f s) (term65 _105011 _105012 s p1 t p2)). Qed.
Lemma lem4379476 {_105011 _105012 : Type'} (f : type686 _105011) (s : _105011 -> Prop) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term132 _105011 _105012 f s p1 t p2) = (term131 _105011 _105012 f s p1 t p2).
Proof. exact (TRANS (@lem4379475 _105011 _105012 f s p1 t p2) (@lem4379474 _105011 _105012 f s p1 t p2)). Qed.
Lemma lem4379481 {_105011 _105012 : Type'} (f : type686 _105011) (s : _105011 -> Prop) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term67 _105011 _105012 f s p1 t p2) = (term133 _105011 _105012 f s p1 t p2).
Proof. exact (@lem17265 (f s) (term65 _105011 _105012 s p1 t p2)). Qed.
Lemma lem4379482 {_105011 : Type'} (P : type686 _105011) : (term99 _105011 P) = (term100 _105011 P).
Proof. exact (@lem18392 (_105011 -> Prop) P). Qed.
Lemma lem4379483 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term134 _105011 _105012 f p1 t p2) = (term135 _105011 _105012 f p1 t p2).
Proof. exact (@lem4379482 _105011 (term69 _105011 _105012 f p1 t p2)). Qed.
Lemma lem4379484 {_105011 _105012 : Type'} (f : type686 _105011) (s : _105011 -> Prop) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term136 _105011 _105012 f p1 t p2 s) = (term67 _105011 _105012 f s p1 t p2).
Proof. exact (eq_refl (term136 _105011 _105012 f p1 t p2 s)). Qed.
Lemma lem4379485 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4379486 {_105011 _105012 : Type'} (f : type686 _105011) (s : _105011 -> Prop) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term137 _105011 _105012 f p1 t p2 s) = (term132 _105011 _105012 f s p1 t p2).
Proof. exact (MK_COMB (@lem4379485) (@lem4379484 _105011 _105012 f s p1 t p2)). Qed.
Lemma lem4379487 {_105011 _105012 : Type'} (f : type686 _105011) (s : _105011 -> Prop) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term137 _105011 _105012 f p1 t p2 s) = (term131 _105011 _105012 f s p1 t p2).
Proof. exact (TRANS (@lem4379486 _105011 _105012 f s p1 t p2) (@lem4379476 _105011 _105012 f s p1 t p2)). Qed.
Lemma lem4379488 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term138 _105011 _105012 f p1 t p2) = (term139 _105011 _105012 f p1 t p2).
Proof. exact (fun_ext (fun s : _105011 -> Prop => @lem4379487 _105011 _105012 f s p1 t p2)). Qed.
Lemma lem4379489 {_105011 : Type'} : (@ex (_105011 -> Prop)) = (@ex (_105011 -> Prop)).
Proof. exact (eq_refl (@ex (_105011 -> Prop))). Qed.
Lemma lem4379490 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term135 _105011 _105012 f p1 t p2) = (term140 _105011 _105012 f p1 t p2).
Proof. exact (MK_COMB (@lem4379489 _105011) (@lem4379488 _105011 _105012 f p1 t p2)). Qed.
Lemma lem4379491 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term134 _105011 _105012 f p1 t p2) = (term140 _105011 _105012 f p1 t p2).
Proof. exact (TRANS (@lem4379483 _105011 _105012 f p1 t p2) (@lem4379490 _105011 _105012 f p1 t p2)). Qed.
Lemma lem4379492 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term69 _105011 _105012 f p1 t p2) = (term141 _105011 _105012 f p1 t p2).
Proof. exact (fun_ext (fun s : _105011 -> Prop => @lem4379481 _105011 _105012 f s p1 t p2)). Qed.
Lemma lem4379493 {_105011 : Type'} : (@all (_105011 -> Prop)) = (@all (_105011 -> Prop)).
Proof. exact (eq_refl (@all (_105011 -> Prop))). Qed.
Lemma lem4379494 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term71 _105011 _105012 f p1 t p2) = (term142 _105011 _105012 f p1 t p2).
Proof. exact (MK_COMB (@lem4379493 _105011) (@lem4379492 _105011 _105012 f p1 t p2)). Qed.
Lemma lem4379495 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4379496 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term143 _105011 _105012 f p1 t p2) = (term144 _105011 _105012 f p1 t p2).
Proof. exact (MK_COMB (@lem4379495) (@lem4379454 _105011 _105012 f p1 t p2)). Qed.
Lemma lem4379497 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term145 _105011 _105012 f p1 t p2) = (term146 _105011 _105012 f p1 t p2).
Proof. exact (MK_COMB (@lem4379496 _105011 _105012 f p1 t p2) (@lem4379494 _105011 _105012 f p1 t p2)). Qed.
Lemma lem4379498 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4379499 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term147 _105011 _105012 f p1 t p2) = (term148 _105011 _105012 f p1 t p2).
Proof. exact (MK_COMB (@lem4379498) (@lem4379457 _105011 _105012 f p1 t p2)). Qed.
Lemma lem4379500 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term149 _105011 _105012 f p1 t p2) = (term150 _105011 _105012 f p1 t p2).
Proof. exact (MK_COMB (@lem4379499 _105011 _105012 f p1 t p2) (@lem4379491 _105011 _105012 f p1 t p2)). Qed.
Lemma lem4379501 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4379502 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term151 _105011 _105012 f p1 t p2) = (term152 _105011 _105012 f p1 t p2).
Proof. exact (MK_COMB (@lem4379501) (@lem4379500 _105011 _105012 f p1 t p2)). Qed.
Lemma lem4379503 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term153 _105011 _105012 f p1 t p2) = (term154 _105011 _105012 f p1 t p2).
Proof. exact (MK_COMB (@lem4379502 _105011 _105012 f p1 t p2) (@lem4379497 _105011 _105012 f p1 t p2)). Qed.
Lemma lem4379504 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term97 _105011 _105012 f p1 t p2) = (term153 _105011 _105012 f p1 t p2).
Proof. exact (@lem17646 (term59 _105011 _105012 f p1 t p2) (term71 _105011 _105012 f p1 t p2)). Qed.
Lemma lem4379505 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term97 _105011 _105012 f p1 t p2) = (term154 _105011 _105012 f p1 t p2).
Proof. exact (TRANS (@lem4379504 _105011 _105012 f p1 t p2) (@lem4379503 _105011 _105012 f p1 t p2)). Qed.
Lemma lem4379660 {A : Type'} (P : Prop) (Q : A -> Prop) : (term155 A P Q) = (term156 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4379661 {_105011 : Type'} (P : Prop) (Q : type686 _105011) : (term157 _105011 P Q) = (term158 _105011 P Q).
Proof. exact (@lem4379660 (_105011 -> Prop) P Q). Qed.
Lemma lem4379662 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term159 _105011 _105012 f p1 t p2) = (term160 _105011 _105012 f p1 t p2).
Proof. exact (@lem4379661 _105011 (term126 _105011 _105012 f p1 t p2) (term139 _105011 _105012 f p1 t p2)). Qed.
Lemma lem4379663 {_105011 _105012 : Type'} (f : type686 _105011) (s : _105011 -> Prop) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term161 _105011 _105012 f p1 t p2 s) = (term131 _105011 _105012 f s p1 t p2).
Proof. exact (eq_refl (term161 _105011 _105012 f p1 t p2 s)). Qed.
Lemma lem4379664 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term162 _105011 _105012 f p1 t p2) = (term139 _105011 _105012 f p1 t p2).
Proof. exact (fun_ext (fun s : _105011 -> Prop => @lem4379663 _105011 _105012 f s p1 t p2)). Qed.
Lemma lem4379665 {_105011 : Type'} : (@ex (_105011 -> Prop)) = (@ex (_105011 -> Prop)).
Proof. exact (eq_refl (@ex (_105011 -> Prop))). Qed.
Lemma lem4379666 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term163 _105011 _105012 f p1 t p2) = (term140 _105011 _105012 f p1 t p2).
Proof. exact (MK_COMB (@lem4379665 _105011) (@lem4379664 _105011 _105012 f p1 t p2)). Qed.
Lemma lem4379667 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term148 _105011 _105012 f p1 t p2) = (term148 _105011 _105012 f p1 t p2).
Proof. exact (eq_refl (term148 _105011 _105012 f p1 t p2)). Qed.
Lemma lem4379668 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term159 _105011 _105012 f p1 t p2) = (term150 _105011 _105012 f p1 t p2).
Proof. exact (MK_COMB (@lem4379667 _105011 _105012 f p1 t p2) (@lem4379666 _105011 _105012 f p1 t p2)). Qed.
Lemma lem4379669 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4379670 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term164 _105011 _105012 f p1 t p2) = (term165 _105011 _105012 f p1 t p2).
Proof. exact (MK_COMB (@lem4379669) (@lem4379668 _105011 _105012 f p1 t p2)). Qed.
Lemma lem4379671 {_105011 _105012 : Type'} (f : type686 _105011) (s : _105011 -> Prop) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term161 _105011 _105012 f p1 t p2 s) = (term131 _105011 _105012 f s p1 t p2).
Proof. exact (eq_refl (term161 _105011 _105012 f p1 t p2 s)). Qed.
Lemma lem4379672 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term148 _105011 _105012 f p1 t p2) = (term148 _105011 _105012 f p1 t p2).
Proof. exact (eq_refl (term148 _105011 _105012 f p1 t p2)). Qed.
Lemma lem4379673 {_105011 _105012 : Type'} (f : type686 _105011) (s : _105011 -> Prop) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term166 _105011 _105012 f p1 t p2 s) = (term167 _105011 _105012 f s p1 t p2).
Proof. exact (MK_COMB (@lem4379672 _105011 _105012 f p1 t p2) (@lem4379671 _105011 _105012 f s p1 t p2)). Qed.
Lemma lem4379674 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term168 _105011 _105012 f p1 t p2) = (term169 _105011 _105012 f p1 t p2).
Proof. exact (fun_ext (fun s : _105011 -> Prop => @lem4379673 _105011 _105012 f s p1 t p2)). Qed.
Lemma lem4379675 {_105011 : Type'} : (@ex (_105011 -> Prop)) = (@ex (_105011 -> Prop)).
Proof. exact (eq_refl (@ex (_105011 -> Prop))). Qed.
Lemma lem4379676 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term160 _105011 _105012 f p1 t p2) = (term170 _105011 _105012 f p1 t p2).
Proof. exact (MK_COMB (@lem4379675 _105011) (@lem4379674 _105011 _105012 f p1 t p2)). Qed.
Lemma lem4379677 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : ((term159 _105011 _105012 f p1 t p2) = (term160 _105011 _105012 f p1 t p2)) = ((term150 _105011 _105012 f p1 t p2) = (term170 _105011 _105012 f p1 t p2)).
Proof. exact (MK_COMB (@lem4379670 _105011 _105012 f p1 t p2) (@lem4379676 _105011 _105012 f p1 t p2)). Qed.
Lemma lem4379678 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term150 _105011 _105012 f p1 t p2) = (term170 _105011 _105012 f p1 t p2).
Proof. exact (EQ_MP (@lem4379677 _105011 _105012 f p1 t p2) (@lem4379662 _105011 _105012 f p1 t p2)). Qed.
Lemma lem4379679 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4379680 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term152 _105011 _105012 f p1 t p2) = (term171 _105011 _105012 f p1 t p2).
Proof. exact (MK_COMB (@lem4379679) (@lem4379678 _105011 _105012 f p1 t p2)). Qed.
Lemma lem4379682 {A : Type'} (P : A -> Prop) (Q : Prop) : (term172 A P Q) = (term173 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4379683 {_105011 : Type'} (P : type686 _105011) (Q : Prop) : (term174 _105011 P Q) = (term175 _105011 P Q).
Proof. exact (@lem4379682 (_105011 -> Prop) P Q). Qed.
Lemma lem4379684 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term176 _105011 _105012 f p1 t p2) = (term177 _105011 _105012 f p1 t p2).
Proof. exact (@lem4379683 _105011 (term115 _105011 f p1) (term119 _105012 t p2)). Qed.
Lemma lem4379685 {_105011 : Type'} (f : type686 _105011) (t : _105011 -> Prop) (p1 : _105011) : (term178 _105011 f p1 t) = (term108 _105011 f t p1).
Proof. exact (eq_refl (term178 _105011 f p1 t)). Qed.
Lemma lem4379686 {_105011 : Type'} (f : type686 _105011) (p1 : _105011) : (term179 _105011 f p1) = (term115 _105011 f p1).
Proof. exact (fun_ext (fun t : _105011 -> Prop => @lem4379685 _105011 f t p1)). Qed.
Lemma lem4379687 {_105011 : Type'} : (@ex (_105011 -> Prop)) = (@ex (_105011 -> Prop)).
Proof. exact (eq_refl (@ex (_105011 -> Prop))). Qed.
Lemma lem4379688 {_105011 : Type'} (f : type686 _105011) (p1 : _105011) : (term180 _105011 f p1) = (term116 _105011 f p1).
Proof. exact (MK_COMB (@lem4379687 _105011) (@lem4379686 _105011 f p1)). Qed.
Lemma lem4379689 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4379690 {_105011 : Type'} (f : type686 _105011) (p1 : _105011) : (term181 _105011 f p1) = (term121 _105011 f p1).
Proof. exact (MK_COMB (@lem4379689) (@lem4379688 _105011 f p1)). Qed.
Lemma lem4379691 {_105012 : Type'} (t : _105012 -> Prop) (p2 : _105012) : (term119 _105012 t p2) = (term119 _105012 t p2).
Proof. exact (eq_refl (term119 _105012 t p2)). Qed.
Lemma lem4379692 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term176 _105011 _105012 f p1 t p2) = (term123 _105011 _105012 f p1 t p2).
Proof. exact (MK_COMB (@lem4379690 _105011 f p1) (@lem4379691 _105012 t p2)). Qed.
Lemma lem4379693 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4379694 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term182 _105011 _105012 f p1 t p2) = (term183 _105011 _105012 f p1 t p2).
Proof. exact (MK_COMB (@lem4379693) (@lem4379692 _105011 _105012 f p1 t p2)). Qed.
Lemma lem4379695 {_105011 : Type'} (f : type686 _105011) (t : _105011 -> Prop) (p1 : _105011) : (term178 _105011 f p1 t) = (term108 _105011 f t p1).
Proof. exact (eq_refl (term178 _105011 f p1 t)). Qed.
Lemma lem4379696 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4379697 {_105011 : Type'} (f : type686 _105011) (t : _105011 -> Prop) (p1 : _105011) : (term184 _105011 f p1 t) = (term185 _105011 f t p1).
Proof. exact (MK_COMB (@lem4379696) (@lem4379695 _105011 f t p1)). Qed.
Lemma lem4379698 {_105012 : Type'} (t : _105012 -> Prop) (p2 : _105012) : (term119 _105012 t p2) = (term119 _105012 t p2).
Proof. exact (eq_refl (term119 _105012 t p2)). Qed.
Lemma lem4379699 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105011 -> Prop) (p1 : _105011) (t' : _105012 -> Prop) (p2 : _105012) : (term186 _105011 _105012 f p1 t t' p2) = (term187 _105011 _105012 f t p1 t' p2).
Proof. exact (MK_COMB (@lem4379697 _105011 f t p1) (@lem4379698 _105012 t' p2)). Qed.
Lemma lem4379700 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term188 _105011 _105012 f p1 t p2) = (term189 _105011 _105012 f p1 t p2).
Proof. exact (fun_ext (fun t' : _105011 -> Prop => @lem4379699 _105011 _105012 f t' p1 t p2)). Qed.
Lemma lem4379701 {_105011 : Type'} : (@ex (_105011 -> Prop)) = (@ex (_105011 -> Prop)).
Proof. exact (eq_refl (@ex (_105011 -> Prop))). Qed.
Lemma lem4379702 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term177 _105011 _105012 f p1 t p2) = (term190 _105011 _105012 f p1 t p2).
Proof. exact (MK_COMB (@lem4379701 _105011) (@lem4379700 _105011 _105012 f p1 t p2)). Qed.
Lemma lem4379703 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : ((term176 _105011 _105012 f p1 t p2) = (term177 _105011 _105012 f p1 t p2)) = ((term123 _105011 _105012 f p1 t p2) = (term190 _105011 _105012 f p1 t p2)).
Proof. exact (MK_COMB (@lem4379694 _105011 _105012 f p1 t p2) (@lem4379702 _105011 _105012 f p1 t p2)). Qed.
Lemma lem4379704 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term123 _105011 _105012 f p1 t p2) = (term190 _105011 _105012 f p1 t p2).
Proof. exact (EQ_MP (@lem4379703 _105011 _105012 f p1 t p2) (@lem4379684 _105011 _105012 f p1 t p2)). Qed.
Lemma lem4379705 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4379706 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term144 _105011 _105012 f p1 t p2) = (term191 _105011 _105012 f p1 t p2).
Proof. exact (MK_COMB (@lem4379705) (@lem4379704 _105011 _105012 f p1 t p2)). Qed.
Lemma lem4379707 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term142 _105011 _105012 f p1 t p2) = (term142 _105011 _105012 f p1 t p2).
Proof. exact (eq_refl (term142 _105011 _105012 f p1 t p2)). Qed.
Lemma lem4379708 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term146 _105011 _105012 f p1 t p2) = (term192 _105011 _105012 f p1 t p2).
Proof. exact (MK_COMB (@lem4379706 _105011 _105012 f p1 t p2) (@lem4379707 _105011 _105012 f p1 t p2)). Qed.
Lemma lem4379710 {A : Type'} (P : A -> Prop) (Q : Prop) : (term193 A P Q) = (term194 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4379711 {_105011 : Type'} (P : type686 _105011) (Q : Prop) : (term195 _105011 P Q) = (term196 _105011 P Q).
Proof. exact (@lem4379710 (_105011 -> Prop) P Q). Qed.
Lemma lem4379712 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term197 _105011 _105012 f p1 t p2) = (term198 _105011 _105012 f p1 t p2).
Proof. exact (@lem4379711 _105011 (term189 _105011 _105012 f p1 t p2) (term142 _105011 _105012 f p1 t p2)). Qed.
Lemma lem4379713 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105011 -> Prop) (p1 : _105011) (t' : _105012 -> Prop) (p2 : _105012) : (term199 _105011 _105012 f p1 t' p2 t) = (term187 _105011 _105012 f t p1 t' p2).
Proof. exact (eq_refl (term199 _105011 _105012 f p1 t' p2 t)). Qed.
Lemma lem4379714 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term200 _105011 _105012 f p1 t p2) = (term189 _105011 _105012 f p1 t p2).
Proof. exact (fun_ext (fun t' : _105011 -> Prop => @lem4379713 _105011 _105012 f t' p1 t p2)). Qed.
Lemma lem4379715 {_105011 : Type'} : (@ex (_105011 -> Prop)) = (@ex (_105011 -> Prop)).
Proof. exact (eq_refl (@ex (_105011 -> Prop))). Qed.
Lemma lem4379716 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term201 _105011 _105012 f p1 t p2) = (term190 _105011 _105012 f p1 t p2).
Proof. exact (MK_COMB (@lem4379715 _105011) (@lem4379714 _105011 _105012 f p1 t p2)). Qed.
Lemma lem4379717 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4379718 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term202 _105011 _105012 f p1 t p2) = (term191 _105011 _105012 f p1 t p2).
Proof. exact (MK_COMB (@lem4379717) (@lem4379716 _105011 _105012 f p1 t p2)). Qed.
Lemma lem4379719 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term142 _105011 _105012 f p1 t p2) = (term142 _105011 _105012 f p1 t p2).
Proof. exact (eq_refl (term142 _105011 _105012 f p1 t p2)). Qed.
Lemma lem4379720 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term197 _105011 _105012 f p1 t p2) = (term192 _105011 _105012 f p1 t p2).
Proof. exact (MK_COMB (@lem4379718 _105011 _105012 f p1 t p2) (@lem4379719 _105011 _105012 f p1 t p2)). Qed.
Lemma lem4379721 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4379722 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term203 _105011 _105012 f p1 t p2) = (term204 _105011 _105012 f p1 t p2).
Proof. exact (MK_COMB (@lem4379721) (@lem4379720 _105011 _105012 f p1 t p2)). Qed.
Lemma lem4379723 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105011 -> Prop) (p1 : _105011) (t' : _105012 -> Prop) (p2 : _105012) : (term199 _105011 _105012 f p1 t' p2 t) = (term187 _105011 _105012 f t p1 t' p2).
Proof. exact (eq_refl (term199 _105011 _105012 f p1 t' p2 t)). Qed.
Lemma lem4379724 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4379725 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105011 -> Prop) (p1 : _105011) (t' : _105012 -> Prop) (p2 : _105012) : (term205 _105011 _105012 f p1 t' p2 t) = (term206 _105011 _105012 f t p1 t' p2).
Proof. exact (MK_COMB (@lem4379724) (@lem4379723 _105011 _105012 f t p1 t' p2)). Qed.
Lemma lem4379726 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term142 _105011 _105012 f p1 t p2) = (term142 _105011 _105012 f p1 t p2).
Proof. exact (eq_refl (term142 _105011 _105012 f p1 t p2)). Qed.
Lemma lem4379727 {_105011 _105012 : Type'} (t : _105011 -> Prop) (f : type686 _105011) (p1 : _105011) (t' : _105012 -> Prop) (p2 : _105012) : (term207 _105011 _105012 t f p1 t' p2) = (term208 _105011 _105012 t f p1 t' p2).
Proof. exact (MK_COMB (@lem4379725 _105011 _105012 f t p1 t' p2) (@lem4379726 _105011 _105012 f p1 t' p2)). Qed.
Lemma lem4379728 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term209 _105011 _105012 f p1 t p2) = (term210 _105011 _105012 f p1 t p2).
Proof. exact (fun_ext (fun t' : _105011 -> Prop => @lem4379727 _105011 _105012 t' f p1 t p2)). Qed.
Lemma lem4379729 {_105011 : Type'} : (@ex (_105011 -> Prop)) = (@ex (_105011 -> Prop)).
Proof. exact (eq_refl (@ex (_105011 -> Prop))). Qed.
Lemma lem4379730 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term198 _105011 _105012 f p1 t p2) = (term211 _105011 _105012 f p1 t p2).
Proof. exact (MK_COMB (@lem4379729 _105011) (@lem4379728 _105011 _105012 f p1 t p2)). Qed.
Lemma lem4379731 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : ((term197 _105011 _105012 f p1 t p2) = (term198 _105011 _105012 f p1 t p2)) = ((term192 _105011 _105012 f p1 t p2) = (term211 _105011 _105012 f p1 t p2)).
Proof. exact (MK_COMB (@lem4379722 _105011 _105012 f p1 t p2) (@lem4379730 _105011 _105012 f p1 t p2)). Qed.
Lemma lem4379732 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term192 _105011 _105012 f p1 t p2) = (term211 _105011 _105012 f p1 t p2).
Proof. exact (EQ_MP (@lem4379731 _105011 _105012 f p1 t p2) (@lem4379712 _105011 _105012 f p1 t p2)). Qed.
Lemma lem4379733 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term146 _105011 _105012 f p1 t p2) = (term211 _105011 _105012 f p1 t p2).
Proof. exact (TRANS (@lem4379708 _105011 _105012 f p1 t p2) (@lem4379732 _105011 _105012 f p1 t p2)). Qed.
Lemma lem4379734 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term154 _105011 _105012 f p1 t p2) = (term212 _105011 _105012 f p1 t p2).
Proof. exact (MK_COMB (@lem4379680 _105011 _105012 f p1 t p2) (@lem4379733 _105011 _105012 f p1 t p2)). Qed.
Lemma lem4379736 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term213 A P Q) = (term214 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4379737 {_105011 : Type'} (P : type686 _105011) (Q : type686 _105011) : (term215 _105011 P Q) = (term216 _105011 P Q).
Proof. exact (@lem4379736 (_105011 -> Prop) P Q). Qed.
Lemma lem4379738 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term217 _105011 _105012 f p1 t p2) = (term218 _105011 _105012 f p1 t p2).
Proof. exact (@lem4379737 _105011 (term169 _105011 _105012 f p1 t p2) (term210 _105011 _105012 f p1 t p2)). Qed.
Lemma lem4379739 {_105011 _105012 : Type'} (f : type686 _105011) (s : _105011 -> Prop) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term219 _105011 _105012 f p1 t p2 s) = (term167 _105011 _105012 f s p1 t p2).
Proof. exact (eq_refl (term219 _105011 _105012 f p1 t p2 s)). Qed.
Lemma lem4379740 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term220 _105011 _105012 f p1 t p2) = (term169 _105011 _105012 f p1 t p2).
Proof. exact (fun_ext (fun s : _105011 -> Prop => @lem4379739 _105011 _105012 f s p1 t p2)). Qed.
Lemma lem4379741 {_105011 : Type'} : (@ex (_105011 -> Prop)) = (@ex (_105011 -> Prop)).
Proof. exact (eq_refl (@ex (_105011 -> Prop))). Qed.
Lemma lem4379742 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term221 _105011 _105012 f p1 t p2) = (term170 _105011 _105012 f p1 t p2).
Proof. exact (MK_COMB (@lem4379741 _105011) (@lem4379740 _105011 _105012 f p1 t p2)). Qed.
Lemma lem4379743 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4379744 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term222 _105011 _105012 f p1 t p2) = (term171 _105011 _105012 f p1 t p2).
Proof. exact (MK_COMB (@lem4379743) (@lem4379742 _105011 _105012 f p1 t p2)). Qed.
Lemma lem4379745 {_105011 _105012 : Type'} (s : _105011 -> Prop) (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term223 _105011 _105012 f p1 t p2 s) = (term208 _105011 _105012 s f p1 t p2).
Proof. exact (eq_refl (term223 _105011 _105012 f p1 t p2 s)). Qed.
Lemma lem4379746 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term224 _105011 _105012 f p1 t p2) = (term210 _105011 _105012 f p1 t p2).
Proof. exact (fun_ext (fun s : _105011 -> Prop => @lem4379745 _105011 _105012 s f p1 t p2)). Qed.
Lemma lem4379747 {_105011 : Type'} : (@ex (_105011 -> Prop)) = (@ex (_105011 -> Prop)).
Proof. exact (eq_refl (@ex (_105011 -> Prop))). Qed.
Lemma lem4379748 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term225 _105011 _105012 f p1 t p2) = (term211 _105011 _105012 f p1 t p2).
Proof. exact (MK_COMB (@lem4379747 _105011) (@lem4379746 _105011 _105012 f p1 t p2)). Qed.
Lemma lem4379749 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term217 _105011 _105012 f p1 t p2) = (term212 _105011 _105012 f p1 t p2).
Proof. exact (MK_COMB (@lem4379744 _105011 _105012 f p1 t p2) (@lem4379748 _105011 _105012 f p1 t p2)). Qed.
Lemma lem4379750 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4379751 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term226 _105011 _105012 f p1 t p2) = (term227 _105011 _105012 f p1 t p2).
Proof. exact (MK_COMB (@lem4379750) (@lem4379749 _105011 _105012 f p1 t p2)). Qed.
Lemma lem4379752 {_105011 _105012 : Type'} (f : type686 _105011) (s : _105011 -> Prop) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term219 _105011 _105012 f p1 t p2 s) = (term167 _105011 _105012 f s p1 t p2).
Proof. exact (eq_refl (term219 _105011 _105012 f p1 t p2 s)). Qed.
Lemma lem4379753 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4379754 {_105011 _105012 : Type'} (f : type686 _105011) (s : _105011 -> Prop) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term228 _105011 _105012 f p1 t p2 s) = (term229 _105011 _105012 f s p1 t p2).
Proof. exact (MK_COMB (@lem4379753) (@lem4379752 _105011 _105012 f s p1 t p2)). Qed.
Lemma lem4379755 {_105011 _105012 : Type'} (s : _105011 -> Prop) (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term223 _105011 _105012 f p1 t p2 s) = (term208 _105011 _105012 s f p1 t p2).
Proof. exact (eq_refl (term223 _105011 _105012 f p1 t p2 s)). Qed.
Lemma lem4379756 {_105011 _105012 : Type'} (s : _105011 -> Prop) (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term230 _105011 _105012 f p1 t p2 s) = (term231 _105011 _105012 s f p1 t p2).
Proof. exact (MK_COMB (@lem4379754 _105011 _105012 f s p1 t p2) (@lem4379755 _105011 _105012 s f p1 t p2)). Qed.
Lemma lem4379757 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term232 _105011 _105012 f p1 t p2) = (term233 _105011 _105012 f p1 t p2).
Proof. exact (fun_ext (fun s : _105011 -> Prop => @lem4379756 _105011 _105012 s f p1 t p2)). Qed.
Lemma lem4379758 {_105011 : Type'} : (@ex (_105011 -> Prop)) = (@ex (_105011 -> Prop)).
Proof. exact (eq_refl (@ex (_105011 -> Prop))). Qed.
Lemma lem4379759 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term218 _105011 _105012 f p1 t p2) = (term234 _105011 _105012 f p1 t p2).
Proof. exact (MK_COMB (@lem4379758 _105011) (@lem4379757 _105011 _105012 f p1 t p2)). Qed.
Lemma lem4379760 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : ((term217 _105011 _105012 f p1 t p2) = (term218 _105011 _105012 f p1 t p2)) = ((term212 _105011 _105012 f p1 t p2) = (term234 _105011 _105012 f p1 t p2)).
Proof. exact (MK_COMB (@lem4379751 _105011 _105012 f p1 t p2) (@lem4379759 _105011 _105012 f p1 t p2)). Qed.
Lemma lem4379761 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term212 _105011 _105012 f p1 t p2) = (term234 _105011 _105012 f p1 t p2).
Proof. exact (EQ_MP (@lem4379760 _105011 _105012 f p1 t p2) (@lem4379738 _105011 _105012 f p1 t p2)). Qed.
Lemma lem4379764 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term235 _105011 _105012 f p1 t p2) = (term235 _105011 _105012 f p1 t p2).
Proof. exact (eq_refl (term235 _105011 _105012 f p1 t p2)). Qed.
Lemma lem4379765 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term235 _105011 _105012 f p1 t p2) = ((term212 _105011 _105012 f p1 t p2) = (term234 _105011 _105012 f p1 t p2)).
Proof. exact (eq_refl (term235 _105011 _105012 f p1 t p2)). Qed.
Lemma lem4379766 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term236 _105011 _105012 f p1 t p2) = (term236 _105011 _105012 f p1 t p2).
Proof. exact (eq_refl (term236 _105011 _105012 f p1 t p2)). Qed.
Lemma lem4379767 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : ((term235 _105011 _105012 f p1 t p2) = (term235 _105011 _105012 f p1 t p2)) = ((term235 _105011 _105012 f p1 t p2) = ((term212 _105011 _105012 f p1 t p2) = (term234 _105011 _105012 f p1 t p2))).
Proof. exact (MK_COMB (@lem4379766 _105011 _105012 f p1 t p2) (@lem4379765 _105011 _105012 f p1 t p2)). Qed.
Lemma lem4379768 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term235 _105011 _105012 f p1 t p2) = ((term212 _105011 _105012 f p1 t p2) = (term234 _105011 _105012 f p1 t p2)).
Proof. exact (eq_refl (term235 _105011 _105012 f p1 t p2)). Qed.
Lemma lem4379769 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4379770 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term236 _105011 _105012 f p1 t p2) = (term237 _105011 _105012 f p1 t p2).
Proof. exact (MK_COMB (@lem4379769) (@lem4379768 _105011 _105012 f p1 t p2)). Qed.
Lemma lem4379771 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : ((term212 _105011 _105012 f p1 t p2) = (term234 _105011 _105012 f p1 t p2)) = ((term212 _105011 _105012 f p1 t p2) = (term234 _105011 _105012 f p1 t p2)).
Proof. exact (eq_refl ((term212 _105011 _105012 f p1 t p2) = (term234 _105011 _105012 f p1 t p2))). Qed.
Lemma lem4379772 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : ((term235 _105011 _105012 f p1 t p2) = ((term212 _105011 _105012 f p1 t p2) = (term234 _105011 _105012 f p1 t p2))) = (((term212 _105011 _105012 f p1 t p2) = (term234 _105011 _105012 f p1 t p2)) = ((term212 _105011 _105012 f p1 t p2) = (term234 _105011 _105012 f p1 t p2))).
Proof. exact (MK_COMB (@lem4379770 _105011 _105012 f p1 t p2) (@lem4379771 _105011 _105012 f p1 t p2)). Qed.
Lemma lem4379773 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : ((term235 _105011 _105012 f p1 t p2) = (term235 _105011 _105012 f p1 t p2)) = (((term212 _105011 _105012 f p1 t p2) = (term234 _105011 _105012 f p1 t p2)) = ((term212 _105011 _105012 f p1 t p2) = (term234 _105011 _105012 f p1 t p2))).
Proof. exact (TRANS (@lem4379767 _105011 _105012 f p1 t p2) (@lem4379772 _105011 _105012 f p1 t p2)). Qed.
Lemma lem4379774 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : ((term212 _105011 _105012 f p1 t p2) = (term234 _105011 _105012 f p1 t p2)) = ((term212 _105011 _105012 f p1 t p2) = (term234 _105011 _105012 f p1 t p2)).
Proof. exact (EQ_MP (@lem4379773 _105011 _105012 f p1 t p2) (@lem4379764 _105011 _105012 f p1 t p2)). Qed.
Lemma lem4379775 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term212 _105011 _105012 f p1 t p2) = (term234 _105011 _105012 f p1 t p2).
Proof. exact (EQ_MP (@lem4379774 _105011 _105012 f p1 t p2) (@lem4379761 _105011 _105012 f p1 t p2)). Qed.
Lemma lem4379777 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term154 _105011 _105012 f p1 t p2) = (term234 _105011 _105012 f p1 t p2).
Proof. exact (TRANS (@lem4379734 _105011 _105012 f p1 t p2) (@lem4379775 _105011 _105012 f p1 t p2)). Qed.
Lemma lem4379778 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term97 _105011 _105012 f p1 t p2) = (term234 _105011 _105012 f p1 t p2).
Proof. exact (TRANS (@lem4379505 _105011 _105012 f p1 t p2) (@lem4379777 _105011 _105012 f p1 t p2)). Qed.
Lemma lem4379779 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) (h1 : term97 _105011 _105012 f p1 t p2) : term234 _105011 _105012 f p1 t p2.
Proof. exact (EQ_MP (@lem4379778 _105011 _105012 f p1 t p2) (@lem4379398 _105011 _105012 f p1 t p2 h1)). Qed.
Lemma lem4379780 {_105011 _105012 : Type'} (s : _105011 -> Prop) (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) (h1 : term231 _105011 _105012 s f p1 t p2) : term231 _105011 _105012 s f p1 t p2.
Proof. exact (h1). Qed.
Lemma lem4379781 {_105011 : Type'} (f : type686 _105011) (x : _105011 -> Prop) (h1 : f x) : f x.
Proof. exact (h1). Qed.
Lemma lem4379786 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4379787 {_105012 : Type'} (f : _105012 -> Prop) (x : _105012) : (f x) = (@I (_105012 -> Prop) f x).
Proof. exact (@lem4379786 _105012 Prop f x). Qed.
Lemma lem4379789 {_105012 : Type'} (t : _105012 -> Prop) (p2 : _105012) : (t p2) = (@I (_105012 -> Prop) t p2).
Proof. exact (@lem4379787 _105012 t p2). Qed.
Lemma lem4379794 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4379795 {_105011 : Type'} (f : _105011 -> Prop) (x : _105011) : (f x) = (@I (_105011 -> Prop) f x).
Proof. exact (@lem4379794 _105011 Prop f x). Qed.
Lemma lem4379797 {_105011 : Type'} (s : _105011 -> Prop) (p1 : _105011) : (s p1) = (@I (_105011 -> Prop) s p1).
Proof. exact (@lem4379795 _105011 s p1). Qed.
Lemma lem4379798 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4379799 {_105011 : Type'} (s : _105011 -> Prop) (p1 : _105011) : (term63 _105011 s p1) = (term238 _105011 s p1).
Proof. exact (MK_COMB (@lem4379798) (@lem4379797 _105011 s p1)). Qed.
Lemma lem4379800 {_105011 _105012 : Type'} (s : _105011 -> Prop) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term65 _105011 _105012 s p1 t p2) = (term239 _105011 _105012 s p1 t p2).
Proof. exact (MK_COMB (@lem4379799 _105011 s p1) (@lem4379789 _105012 t p2)). Qed.
Lemma lem4379801 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4379806 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4379807 {_105011 : Type'} (f : type686 _105011) (x : _105011 -> Prop) : (f x) = (@I ((_105011 -> Prop) -> Prop) f x).
Proof. exact (@lem4379806 (_105011 -> Prop) Prop f x). Qed.
Lemma lem4379809 {_105011 : Type'} (f : type686 _105011) (s : _105011 -> Prop) : (f s) = (@I ((_105011 -> Prop) -> Prop) f s).
Proof. exact (@lem4379807 _105011 f s). Qed.
Lemma lem4379810 {_105011 : Type'} (f : type686 _105011) (s : _105011 -> Prop) : (term10 _105011 f s) = (term240 _105011 f s).
Proof. exact (MK_COMB (@lem4379801) (@lem4379809 _105011 f s)). Qed.
Lemma lem4379811 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4379812 {_105011 : Type'} (f : type686 _105011) (s : _105011 -> Prop) : (term241 _105011 f s) = (term242 _105011 f s).
Proof. exact (MK_COMB (@lem4379811) (@lem4379810 _105011 f s)). Qed.
Lemma lem4379813 {_105011 _105012 : Type'} (f : type686 _105011) (s : _105011 -> Prop) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term133 _105011 _105012 f s p1 t p2) = (term243 _105011 _105012 f s p1 t p2).
Proof. exact (MK_COMB (@lem4379812 _105011 f s) (@lem4379800 _105011 _105012 s p1 t p2)). Qed.
Lemma lem4379814 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term141 _105011 _105012 f p1 t p2) = (term244 _105011 _105012 f p1 t p2).
Proof. exact (fun_ext (fun s : _105011 -> Prop => @lem4379813 _105011 _105012 f s p1 t p2)). Qed.
Lemma lem4379815 {_105011 : Type'} : (@all (_105011 -> Prop)) = (@all (_105011 -> Prop)).
Proof. exact (eq_refl (@all (_105011 -> Prop))). Qed.
Lemma lem4379816 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term142 _105011 _105012 f p1 t p2) = (term245 _105011 _105012 f p1 t p2).
Proof. exact (MK_COMB (@lem4379815 _105011) (@lem4379814 _105011 _105012 f p1 t p2)). Qed.
Lemma lem4379817 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4379822 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4379823 {_105012 : Type'} (f : _105012 -> Prop) (x : _105012) : (f x) = (@I (_105012 -> Prop) f x).
Proof. exact (@lem4379822 _105012 Prop f x). Qed.
Lemma lem4379825 {_105012 : Type'} (t : _105012 -> Prop) (p2 : _105012) : (t p2) = (@I (_105012 -> Prop) t p2).
Proof. exact (@lem4379823 _105012 t p2). Qed.
Lemma lem4379826 {_105012 : Type'} (t : _105012 -> Prop) (p2 : _105012) : (term119 _105012 t p2) = (term246 _105012 t p2).
Proof. exact (MK_COMB (@lem4379817) (@lem4379825 _105012 t p2)). Qed.
Lemma lem4379827 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4379832 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4379833 {_105011 : Type'} (f : _105011 -> Prop) (x : _105011) : (f x) = (@I (_105011 -> Prop) f x).
Proof. exact (@lem4379832 _105011 Prop f x). Qed.
Lemma lem4379835 {_105011 : Type'} (s : _105011 -> Prop) (p1 : _105011) : (s p1) = (@I (_105011 -> Prop) s p1).
Proof. exact (@lem4379833 _105011 s p1). Qed.
Lemma lem4379836 {_105011 : Type'} (s : _105011 -> Prop) (p1 : _105011) : (term119 _105011 s p1) = (term246 _105011 s p1).
Proof. exact (MK_COMB (@lem4379827) (@lem4379835 _105011 s p1)). Qed.
Lemma lem4379841 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4379842 {_105011 : Type'} (f : type686 _105011) (x : _105011 -> Prop) : (f x) = (@I ((_105011 -> Prop) -> Prop) f x).
Proof. exact (@lem4379841 (_105011 -> Prop) Prop f x). Qed.
Lemma lem4379844 {_105011 : Type'} (f : type686 _105011) (s : _105011 -> Prop) : (f s) = (@I ((_105011 -> Prop) -> Prop) f s).
Proof. exact (@lem4379842 _105011 f s). Qed.
Lemma lem4379845 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4379846 {_105011 : Type'} (f : type686 _105011) (s : _105011 -> Prop) : (term129 _105011 f s) = (term247 _105011 f s).
Proof. exact (MK_COMB (@lem4379845) (@lem4379844 _105011 f s)). Qed.
Lemma lem4379847 {_105011 : Type'} (f : type686 _105011) (s : _105011 -> Prop) (p1 : _105011) : (term108 _105011 f s p1) = (term248 _105011 f s p1).
Proof. exact (MK_COMB (@lem4379846 _105011 f s) (@lem4379836 _105011 s p1)). Qed.
Lemma lem4379848 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4379849 {_105011 : Type'} (f : type686 _105011) (s : _105011 -> Prop) (p1 : _105011) : (term185 _105011 f s p1) = (term249 _105011 f s p1).
Proof. exact (MK_COMB (@lem4379848) (@lem4379847 _105011 f s p1)). Qed.
Lemma lem4379850 {_105011 _105012 : Type'} (f : type686 _105011) (s : _105011 -> Prop) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term187 _105011 _105012 f s p1 t p2) = (term250 _105011 _105012 f s p1 t p2).
Proof. exact (MK_COMB (@lem4379849 _105011 f s p1) (@lem4379826 _105012 t p2)). Qed.
Lemma lem4379851 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4379852 {_105011 _105012 : Type'} (f : type686 _105011) (s : _105011 -> Prop) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term206 _105011 _105012 f s p1 t p2) = (term251 _105011 _105012 f s p1 t p2).
Proof. exact (MK_COMB (@lem4379851) (@lem4379850 _105011 _105012 f s p1 t p2)). Qed.
Lemma lem4379853 {_105011 _105012 : Type'} (s : _105011 -> Prop) (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term208 _105011 _105012 s f p1 t p2) = (term252 _105011 _105012 s f p1 t p2).
Proof. exact (MK_COMB (@lem4379852 _105011 _105012 f s p1 t p2) (@lem4379816 _105011 _105012 f p1 t p2)). Qed.
Lemma lem4379854 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4379859 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4379860 {_105012 : Type'} (f : _105012 -> Prop) (x : _105012) : (f x) = (@I (_105012 -> Prop) f x).
Proof. exact (@lem4379859 _105012 Prop f x). Qed.
Lemma lem4379862 {_105012 : Type'} (t : _105012 -> Prop) (p2 : _105012) : (t p2) = (@I (_105012 -> Prop) t p2).
Proof. exact (@lem4379860 _105012 t p2). Qed.
Lemma lem4379863 {_105012 : Type'} (t : _105012 -> Prop) (p2 : _105012) : (term119 _105012 t p2) = (term246 _105012 t p2).
Proof. exact (MK_COMB (@lem4379854) (@lem4379862 _105012 t p2)). Qed.
Lemma lem4379864 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4379869 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4379870 {_105011 : Type'} (f : _105011 -> Prop) (x : _105011) : (f x) = (@I (_105011 -> Prop) f x).
Proof. exact (@lem4379869 _105011 Prop f x). Qed.
Lemma lem4379872 {_105011 : Type'} (s : _105011 -> Prop) (p1 : _105011) : (s p1) = (@I (_105011 -> Prop) s p1).
Proof. exact (@lem4379870 _105011 s p1). Qed.
Lemma lem4379873 {_105011 : Type'} (s : _105011 -> Prop) (p1 : _105011) : (term119 _105011 s p1) = (term246 _105011 s p1).
Proof. exact (MK_COMB (@lem4379864) (@lem4379872 _105011 s p1)). Qed.
Lemma lem4379874 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4379875 {_105011 : Type'} (s : _105011 -> Prop) (p1 : _105011) : (term253 _105011 s p1) = (term254 _105011 s p1).
Proof. exact (MK_COMB (@lem4379874) (@lem4379873 _105011 s p1)). Qed.
Lemma lem4379876 {_105011 _105012 : Type'} (s : _105011 -> Prop) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term128 _105011 _105012 s p1 t p2) = (term255 _105011 _105012 s p1 t p2).
Proof. exact (MK_COMB (@lem4379875 _105011 s p1) (@lem4379863 _105012 t p2)). Qed.
Lemma lem4379881 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4379882 {_105011 : Type'} (f : type686 _105011) (x : _105011 -> Prop) : (f x) = (@I ((_105011 -> Prop) -> Prop) f x).
Proof. exact (@lem4379881 (_105011 -> Prop) Prop f x). Qed.
Lemma lem4379884 {_105011 : Type'} (f : type686 _105011) (s : _105011 -> Prop) : (f s) = (@I ((_105011 -> Prop) -> Prop) f s).
Proof. exact (@lem4379882 _105011 f s). Qed.
Lemma lem4379885 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4379886 {_105011 : Type'} (f : type686 _105011) (s : _105011 -> Prop) : (term129 _105011 f s) = (term247 _105011 f s).
Proof. exact (MK_COMB (@lem4379885) (@lem4379884 _105011 f s)). Qed.
Lemma lem4379887 {_105011 _105012 : Type'} (f : type686 _105011) (s : _105011 -> Prop) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term131 _105011 _105012 f s p1 t p2) = (term256 _105011 _105012 f s p1 t p2).
Proof. exact (MK_COMB (@lem4379886 _105011 f s) (@lem4379876 _105011 _105012 s p1 t p2)). Qed.
Lemma lem4379892 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4379893 {_105012 : Type'} (f : _105012 -> Prop) (x : _105012) : (f x) = (@I (_105012 -> Prop) f x).
Proof. exact (@lem4379892 _105012 Prop f x). Qed.
Lemma lem4379895 {_105012 : Type'} (t : _105012 -> Prop) (p2 : _105012) : (t p2) = (@I (_105012 -> Prop) t p2).
Proof. exact (@lem4379893 _105012 t p2). Qed.
Lemma lem4379900 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4379901 {_105011 : Type'} (f : _105011 -> Prop) (x : _105011) : (f x) = (@I (_105011 -> Prop) f x).
Proof. exact (@lem4379900 _105011 Prop f x). Qed.
Lemma lem4379903 {_105011 : Type'} (t : _105011 -> Prop) (p1 : _105011) : (t p1) = (@I (_105011 -> Prop) t p1).
Proof. exact (@lem4379901 _105011 t p1). Qed.
Lemma lem4379904 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4379909 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4379910 {_105011 : Type'} (f : type686 _105011) (x : _105011 -> Prop) : (f x) = (@I ((_105011 -> Prop) -> Prop) f x).
Proof. exact (@lem4379909 (_105011 -> Prop) Prop f x). Qed.
Lemma lem4379912 {_105011 : Type'} (f : type686 _105011) (t : _105011 -> Prop) : (f t) = (@I ((_105011 -> Prop) -> Prop) f t).
Proof. exact (@lem4379910 _105011 f t). Qed.
Lemma lem4379913 {_105011 : Type'} (f : type686 _105011) (t : _105011 -> Prop) : (term10 _105011 f t) = (term240 _105011 f t).
Proof. exact (MK_COMB (@lem4379904) (@lem4379912 _105011 f t)). Qed.
Lemma lem4379914 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4379915 {_105011 : Type'} (f : type686 _105011) (t : _105011 -> Prop) : (term241 _105011 f t) = (term242 _105011 f t).
Proof. exact (MK_COMB (@lem4379914) (@lem4379913 _105011 f t)). Qed.
Lemma lem4379916 {_105011 : Type'} (f : type686 _105011) (t : _105011 -> Prop) (p1 : _105011) : (term109 _105011 f t p1) = (term257 _105011 f t p1).
Proof. exact (MK_COMB (@lem4379915 _105011 f t) (@lem4379903 _105011 t p1)). Qed.
Lemma lem4379917 {_105011 : Type'} (f : type686 _105011) (p1 : _105011) : (term117 _105011 f p1) = (term258 _105011 f p1).
Proof. exact (fun_ext (fun t : _105011 -> Prop => @lem4379916 _105011 f t p1)). Qed.
Lemma lem4379918 {_105011 : Type'} : (@all (_105011 -> Prop)) = (@all (_105011 -> Prop)).
Proof. exact (eq_refl (@all (_105011 -> Prop))). Qed.
Lemma lem4379919 {_105011 : Type'} (f : type686 _105011) (p1 : _105011) : (term118 _105011 f p1) = (term259 _105011 f p1).
Proof. exact (MK_COMB (@lem4379918 _105011) (@lem4379917 _105011 f p1)). Qed.
Lemma lem4379920 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4379921 {_105011 : Type'} (f : type686 _105011) (p1 : _105011) : (term125 _105011 f p1) = (term260 _105011 f p1).
Proof. exact (MK_COMB (@lem4379920) (@lem4379919 _105011 f p1)). Qed.
Lemma lem4379922 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term126 _105011 _105012 f p1 t p2) = (term261 _105011 _105012 f p1 t p2).
Proof. exact (MK_COMB (@lem4379921 _105011 f p1) (@lem4379895 _105012 t p2)). Qed.
Lemma lem4379923 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4379924 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term148 _105011 _105012 f p1 t p2) = (term262 _105011 _105012 f p1 t p2).
Proof. exact (MK_COMB (@lem4379923) (@lem4379922 _105011 _105012 f p1 t p2)). Qed.
Lemma lem4379925 {_105011 _105012 : Type'} (f : type686 _105011) (s : _105011 -> Prop) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term167 _105011 _105012 f s p1 t p2) = (term263 _105011 _105012 f s p1 t p2).
Proof. exact (MK_COMB (@lem4379924 _105011 _105012 f p1 t p2) (@lem4379887 _105011 _105012 f s p1 t p2)). Qed.
Lemma lem4379926 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4379927 {_105011 _105012 : Type'} (f : type686 _105011) (s : _105011 -> Prop) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term229 _105011 _105012 f s p1 t p2) = (term264 _105011 _105012 f s p1 t p2).
Proof. exact (MK_COMB (@lem4379926) (@lem4379925 _105011 _105012 f s p1 t p2)). Qed.
Lemma lem4379928 {_105011 _105012 : Type'} (s : _105011 -> Prop) (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) : (term231 _105011 _105012 s f p1 t p2) = (term265 _105011 _105012 s f p1 t p2).
Proof. exact (MK_COMB (@lem4379927 _105011 _105012 f s p1 t p2) (@lem4379853 _105011 _105012 s f p1 t p2)). Qed.
Lemma lem4379929 {_105011 _105012 : Type'} (s : _105011 -> Prop) (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) (h1 : term231 _105011 _105012 s f p1 t p2) : term265 _105011 _105012 s f p1 t p2.
Proof. exact (EQ_MP (@lem4379928 _105011 _105012 s f p1 t p2) (@lem4379780 _105011 _105012 s f p1 t p2 h1)). Qed.
Lemma lem4379934 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4379936 {_105011 : Type'} (f : type686 _105011) (x : _105011 -> Prop) : (f x) = (@I ((_105011 -> Prop) -> Prop) f x).
Proof. exact (@lem4379934 (_105011 -> Prop) Prop f x). Qed.
Lemma lem4379938 {_105011 _105012 : Type'} (f : type686 _105011) (s : _105011 -> Prop) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) (h1 : term263 _105011 _105012 f s p1 t p2) : term263 _105011 _105012 f s p1 t p2.
Proof. exact (h1). Qed.
Lemma lem4379939 {_105011 _105012 : Type'} (s : _105011 -> Prop) (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) (h1 : term252 _105011 _105012 s f p1 t p2) : term252 _105011 _105012 s f p1 t p2.
Proof. exact (h1). Qed.
Lemma lem4379940 {_105011 _105012 : Type'} (f : type686 _105011) (s : _105011 -> Prop) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) (h1 : term263 _105011 _105012 f s p1 t p2) : term256 _105011 _105012 f s p1 t p2.
Proof. exact (proj2 (@lem4379938 _105011 _105012 f s p1 t p2 h1)). Qed.
Lemma lem4379941 {_105011 _105012 : Type'} (f : type686 _105011) (s : _105011 -> Prop) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) (h1 : term263 _105011 _105012 f s p1 t p2) : term261 _105011 _105012 f p1 t p2.
Proof. exact (proj1 (@lem4379938 _105011 _105012 f s p1 t p2 h1)). Qed.
Lemma lem4379942 {_105011 _105012 : Type'} (f : type686 _105011) (s : _105011 -> Prop) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) (h1 : term263 _105011 _105012 f s p1 t p2) : term255 _105011 _105012 s p1 t p2.
Proof. exact (proj2 (@lem4379940 _105011 _105012 f s p1 t p2 h1)). Qed.
Lemma lem4379945 {_105011 _105012 : Type'} (f : type686 _105011) (s : _105011 -> Prop) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) (h1 : term263 _105011 _105012 f s p1 t p2) : term259 _105011 f p1.
Proof. exact (proj1 (@lem4379941 _105011 _105012 f s p1 t p2 h1)). Qed.
Lemma lem4379948 {_105011 _105012 : Type'} (s : _105011 -> Prop) (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) (h1 : term252 _105011 _105012 s f p1 t p2) : term245 _105011 _105012 f p1 t p2.
Proof. exact (proj2 (@lem4379939 _105011 _105012 s f p1 t p2 h1)). Qed.
Lemma lem4379949 {_105011 _105012 : Type'} (s : _105011 -> Prop) (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) (h1 : term252 _105011 _105012 s f p1 t p2) : term250 _105011 _105012 f s p1 t p2.
Proof. exact (proj1 (@lem4379939 _105011 _105012 s f p1 t p2 h1)). Qed.
Lemma lem4379950 {_105011 : Type'} (f : type686 _105011) (s : _105011 -> Prop) (p1 : _105011) (h1 : term248 _105011 f s p1) : term248 _105011 f s p1.
Proof. exact (h1). Qed.
Lemma lem4379969 {_105011 : Type'} (f : type686 _105011) (t : _105011 -> Prop) (p1 : _105011) : (term257 _105011 f t p1) = (term257 _105011 f t p1).
Proof. exact (eq_refl (term257 _105011 f t p1)). Qed.
Lemma lem4379970 {_105011 : Type'} (f : type686 _105011) (p1 : _105011) : (term258 _105011 f p1) = (term258 _105011 f p1).
Proof. exact (fun_ext (fun t : _105011 -> Prop => @lem4379969 _105011 f t p1)). Qed.
Lemma lem4379971 {_105011 : Type'} : (@all (_105011 -> Prop)) = (@all (_105011 -> Prop)).
Proof. exact (eq_refl (@all (_105011 -> Prop))). Qed.
Lemma lem4379973 {_105011 : Type'} (f : type686 _105011) (p1 : _105011) : (term259 _105011 f p1) = (term259 _105011 f p1).
Proof. exact (MK_COMB (@lem4379971 _105011) (@lem4379970 _105011 f p1)). Qed.
Lemma lem4379974 {_105011 _105012 : Type'} (f : type686 _105011) (s : _105011 -> Prop) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) (h1 : term263 _105011 _105012 f s p1 t p2) : term259 _105011 f p1.
Proof. exact (EQ_MP (@lem4379973 _105011 f p1) (@lem4379945 _105011 _105012 f s p1 t p2 h1)). Qed.
Lemma lem4379982 {_105011 : Type'} (s : _105011 -> Prop) (p1 : _105011) (h1 : term246 _105011 s p1) : term246 _105011 s p1.
Proof. exact (h1). Qed.
Lemma lem4380011 {_105012 : Type'} (t : _105012 -> Prop) (p2 : _105012) (h1 : term246 _105012 t p2) : term246 _105012 t p2.
Proof. exact (h1). Qed.
Lemma lem4380033 {_105011 _105012 : Type'} (p1 : _105011) (f : type686 _105011) (s : _105011 -> Prop) (t : _105012 -> Prop) (p2 : _105012) : (term243 _105011 _105012 f s p1 t p2) = (term266 _105011 _105012 p1 f s t p2).
Proof. exact (@lem19490 (@I (_105011 -> Prop) s p1) (term240 _105011 f s) (@I (_105012 -> Prop) t p2)). Qed.
Lemma lem4380034 {_105011 _105012 : Type'} (p1 : _105011) (f : type686 _105011) (t : _105012 -> Prop) (p2 : _105012) : (term244 _105011 _105012 f p1 t p2) = (term267 _105011 _105012 p1 f t p2).
Proof. exact (fun_ext (fun s : _105011 -> Prop => @lem4380033 _105011 _105012 p1 f s t p2)). Qed.
Lemma lem4380035 {_105011 : Type'} : (@all (_105011 -> Prop)) = (@all (_105011 -> Prop)).
Proof. exact (eq_refl (@all (_105011 -> Prop))). Qed.
Lemma lem4380037 {_105011 _105012 : Type'} (p1 : _105011) (f : type686 _105011) (t : _105012 -> Prop) (p2 : _105012) : (term245 _105011 _105012 f p1 t p2) = (term268 _105011 _105012 p1 f t p2).
Proof. exact (MK_COMB (@lem4380035 _105011) (@lem4380034 _105011 _105012 p1 f t p2)). Qed.
Lemma lem4380038 {_105011 _105012 : Type'} (s : _105011 -> Prop) (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) (h1 : term252 _105011 _105012 s f p1 t p2) : term268 _105011 _105012 p1 f t p2.
Proof. exact (EQ_MP (@lem4380037 _105011 _105012 p1 f t p2) (@lem4379948 _105011 _105012 s f p1 t p2 h1)). Qed.
Lemma lem4380068 {_105011 _105012 : Type'} (p1 : _105011) (f : type686 _105011) (s : _105011 -> Prop) (t : _105012 -> Prop) (p2 : _105012) : (term243 _105011 _105012 f s p1 t p2) = (term266 _105011 _105012 p1 f s t p2).
Proof. exact (@lem19490 (@I (_105011 -> Prop) s p1) (term240 _105011 f s) (@I (_105012 -> Prop) t p2)). Qed.
Lemma lem4380069 {_105011 _105012 : Type'} (p1 : _105011) (f : type686 _105011) (t : _105012 -> Prop) (p2 : _105012) : (term244 _105011 _105012 f p1 t p2) = (term267 _105011 _105012 p1 f t p2).
Proof. exact (fun_ext (fun s : _105011 -> Prop => @lem4380068 _105011 _105012 p1 f s t p2)). Qed.
Lemma lem4380070 {_105011 : Type'} : (@all (_105011 -> Prop)) = (@all (_105011 -> Prop)).
Proof. exact (eq_refl (@all (_105011 -> Prop))). Qed.
Lemma lem4380072 {_105011 _105012 : Type'} (p1 : _105011) (f : type686 _105011) (t : _105012 -> Prop) (p2 : _105012) : (term245 _105011 _105012 f p1 t p2) = (term268 _105011 _105012 p1 f t p2).
Proof. exact (MK_COMB (@lem4380070 _105011) (@lem4380069 _105011 _105012 p1 f t p2)). Qed.
Lemma lem4380073 {_105011 _105012 : Type'} (s : _105011 -> Prop) (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) (h1 : term252 _105011 _105012 s f p1 t p2) : term268 _105011 _105012 p1 f t p2.
Proof. exact (EQ_MP (@lem4380072 _105011 _105012 p1 f t p2) (@lem4379948 _105011 _105012 s f p1 t p2 h1)). Qed.
Lemma lem4380077 {_105012 : Type'} (t : _105012 -> Prop) (p2 : _105012) (h1 : term246 _105012 t p2) : term246 _105012 t p2.
Proof. exact (h1). Qed.
Lemma lem4380078 {_105011 _105012 : Type'} (_50042 : _105011 -> Prop) (f : type686 _105011) (s : _105011 -> Prop) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) (h1 : term263 _105011 _105012 f s p1 t p2) : term269 _105011 f p1 _50042.
Proof. exact (@lem4379974 _105011 _105012 f s p1 t p2 h1 _50042). Qed.
Lemma lem4380079 {_105011 : Type'} (f : type686 _105011) (_50042 : _105011 -> Prop) (p1 : _105011) : (term269 _105011 f p1 _50042) = (term257 _105011 f _50042 p1).
Proof. exact (eq_refl (term269 _105011 f p1 _50042)). Qed.
Lemma lem4380084 {_105011 _105012 : Type'} (_50044 : _105011 -> Prop) (s : _105011 -> Prop) (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) (h1 : term252 _105011 _105012 s f p1 t p2) : term270 _105011 _105012 p1 f t p2 _50044.
Proof. exact (@lem4380038 _105011 _105012 s f p1 t p2 h1 _50044). Qed.
Lemma lem4380085 {_105011 _105012 : Type'} (p1 : _105011) (f : type686 _105011) (_50044 : _105011 -> Prop) (t : _105012 -> Prop) (p2 : _105012) : (term270 _105011 _105012 p1 f t p2 _50044) = (term266 _105011 _105012 p1 f _50044 t p2).
Proof. exact (eq_refl (term270 _105011 _105012 p1 f t p2 _50044)). Qed.
Lemma lem4380086 {_105011 _105012 : Type'} (_50044 : _105011 -> Prop) (s : _105011 -> Prop) (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) (h1 : term252 _105011 _105012 s f p1 t p2) : term266 _105011 _105012 p1 f _50044 t p2.
Proof. exact (EQ_MP (@lem4380085 _105011 _105012 p1 f _50044 t p2) (@lem4380084 _105011 _105012 _50044 s f p1 t p2 h1)). Qed.
Lemma lem4380087 {_105011 _105012 : Type'} (_50045 : _105011 -> Prop) (s : _105011 -> Prop) (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) (h1 : term252 _105011 _105012 s f p1 t p2) : term270 _105011 _105012 p1 f t p2 _50045.
Proof. exact (@lem4380073 _105011 _105012 s f p1 t p2 h1 _50045). Qed.
Lemma lem4380088 {_105011 _105012 : Type'} (p1 : _105011) (f : type686 _105011) (_50045 : _105011 -> Prop) (t : _105012 -> Prop) (p2 : _105012) : (term270 _105011 _105012 p1 f t p2 _50045) = (term266 _105011 _105012 p1 f _50045 t p2).
Proof. exact (eq_refl (term270 _105011 _105012 p1 f t p2 _50045)). Qed.
Lemma lem4380089 {_105011 _105012 : Type'} (_50045 : _105011 -> Prop) (s : _105011 -> Prop) (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) (h1 : term252 _105011 _105012 s f p1 t p2) : term266 _105011 _105012 p1 f _50045 t p2.
Proof. exact (EQ_MP (@lem4380088 _105011 _105012 p1 f _50045 t p2) (@lem4380087 _105011 _105012 _50045 s f p1 t p2 h1)). Qed.
Lemma lem4380103 {_105011 _105012 : Type'} (_50042 : _105011 -> Prop) (f : type686 _105011) (s : _105011 -> Prop) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) (h1 : term263 _105011 _105012 f s p1 t p2) : term257 _105011 f _50042 p1.
Proof. exact (EQ_MP (@lem4380079 _105011 f _50042 p1) (@lem4380078 _105011 _105012 _50042 f s p1 t p2 h1)). Qed.
Lemma lem4380107 {_105011 : Type'} (s : _105011 -> Prop) (p1 : _105011) (h1 : term246 _105011 s p1) : term246 _105011 s p1.
Proof. exact (h1). Qed.
Lemma lem4380121 {_105012 : Type'} (t : _105012 -> Prop) (p2 : _105012) (h1 : term246 _105012 t p2) : term246 _105012 t p2.
Proof. exact (h1). Qed.
Lemma lem4380127 {_105011 : Type'} (f : type686 _105011) (s : _105011 -> Prop) (p1 : _105011) (h1 : term248 _105011 f s p1) : term246 _105011 s p1.
Proof. exact (proj2 (@lem4379950 _105011 f s p1 h1)). Qed.
Lemma lem4380133 {_105011 _105012 : Type'} (_50044 : _105011 -> Prop) (s : _105011 -> Prop) (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) (h1 : term252 _105011 _105012 s f p1 t p2) : term257 _105011 f _50044 p1.
Proof. exact (proj1 (@lem4380086 _105011 _105012 _50044 s f p1 t p2 h1)). Qed.
Lemma lem4380143 {_105012 : Type'} (t : _105012 -> Prop) (p2 : _105012) (h1 : term246 _105012 t p2) : term246 _105012 t p2.
Proof. exact (h1). Qed.
Lemma lem4380155 {_105011 _105012 : Type'} (_50045 : _105011 -> Prop) (s : _105011 -> Prop) (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) (h1 : term252 _105011 _105012 s f p1 t p2) : term271 _105011 _105012 f _50045 t p2.
Proof. exact (proj2 (@lem4380089 _105011 _105012 _50045 s f p1 t p2 h1)). Qed.
Lemma lem4380157 {_105011 _105012 : Type'} (f : type686 _105011) (s : _105011 -> Prop) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) (h1 : term263 _105011 _105012 f s p1 t p2) : @I ((_105011 -> Prop) -> Prop) f s.
Proof. exact (proj1 (@lem4379940 _105011 _105012 f s p1 t p2 h1)). Qed.
Lemma lem4380158 {_105011 _105012 : Type'} (f : type686 _105011) (s : _105011 -> Prop) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) (h1 : term263 _105011 _105012 f s p1 t p2) : term272 _105011 f s.
Proof. exact (fun h0 : term240 _105011 f s => @lem4380157 _105011 _105012 f s p1 t p2 h1). Qed.
Lemma lem4380160 (p : Prop) : (term273 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4380161 {_105011 : Type'} (f : type686 _105011) (s : _105011 -> Prop) : (term272 _105011 f s) = (@I ((_105011 -> Prop) -> Prop) f s).
Proof. exact (@lem4380160 (@I ((_105011 -> Prop) -> Prop) f s)). Qed.
Lemma lem4380162 {_105011 _105012 : Type'} (f : type686 _105011) (s : _105011 -> Prop) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) (h1 : term263 _105011 _105012 f s p1 t p2) : @I ((_105011 -> Prop) -> Prop) f s.
Proof. exact (EQ_MP (@lem4380161 _105011 f s) (@lem4380158 _105011 _105012 f s p1 t p2 h1)). Qed.
Lemma lem4380168 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4380169 {_105011 : Type'} (p1 : _105011) (f : type686 _105011) (_50042 : _105011 -> Prop) : (term257 _105011 f _50042 p1) = (term274 _105011 p1 f _50042).
Proof. exact (@lem4380168 (@I (_105011 -> Prop) _50042 p1) (term240 _105011 f _50042)). Qed.
Lemma lem4380175 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4380176 {_105011 : Type'} (p1 : _105011) (f : type686 _105011) (_50042 : _105011 -> Prop) : (term275 _105011 f _50042 p1) = (term276 _105011 p1 f _50042).
Proof. exact (MK_COMB (@lem4380175) (@lem4380169 _105011 p1 f _50042)). Qed.
Lemma lem4380182 {_105011 : Type'} (p1 : _105011) (f : type686 _105011) (_50042 : _105011 -> Prop) : (term274 _105011 p1 f _50042) = (term274 _105011 p1 f _50042).
Proof. exact (eq_refl (term274 _105011 p1 f _50042)). Qed.
Lemma lem4380183 {_105011 : Type'} (p1 : _105011) (f : type686 _105011) (_50042 : _105011 -> Prop) : ((term257 _105011 f _50042 p1) = (term274 _105011 p1 f _50042)) = ((term274 _105011 p1 f _50042) = (term274 _105011 p1 f _50042)).
Proof. exact (MK_COMB (@lem4380176 _105011 p1 f _50042) (@lem4380182 _105011 p1 f _50042)). Qed.
Lemma lem4380185 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4380186 (x : Prop) : (x = x) = True.
Proof. exact (@lem4380185 Prop x). Qed.
Lemma lem4380187 {_105011 : Type'} (p1 : _105011) (f : type686 _105011) (_50042 : _105011 -> Prop) : ((term274 _105011 p1 f _50042) = (term274 _105011 p1 f _50042)) = True.
Proof. exact (@lem4380186 (term274 _105011 p1 f _50042)). Qed.
Lemma lem4380188 {_105011 : Type'} (p1 : _105011) (f : type686 _105011) (_50042 : _105011 -> Prop) : ((term257 _105011 f _50042 p1) = (term274 _105011 p1 f _50042)) = True.
Proof. exact (TRANS (@lem4380183 _105011 p1 f _50042) (@lem4380187 _105011 p1 f _50042)). Qed.
Lemma lem4380189 {_105011 : Type'} (p1 : _105011) (f : type686 _105011) (_50042 : _105011 -> Prop) : True = ((term257 _105011 f _50042 p1) = (term274 _105011 p1 f _50042)).
Proof. exact (SYM (@lem4380188 _105011 p1 f _50042)). Qed.
Lemma lem4380190 {_105011 : Type'} (p1 : _105011) (f : type686 _105011) (_50042 : _105011 -> Prop) : (term257 _105011 f _50042 p1) = (term274 _105011 p1 f _50042).
Proof. exact (EQ_MP (@lem4380189 _105011 p1 f _50042) (@lem0)). Qed.
Lemma lem4380191 {_105011 _105012 : Type'} (_50042 : _105011 -> Prop) (f : type686 _105011) (s : _105011 -> Prop) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) (h1 : term263 _105011 _105012 f s p1 t p2) : term274 _105011 p1 f _50042.
Proof. exact (EQ_MP (@lem4380190 _105011 p1 f _50042) (@lem4380103 _105011 _105012 _50042 f s p1 t p2 h1)). Qed.
Lemma lem4380193 (b : Prop) (a : Prop) : (a \/ b) = (term277 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4380194 {_105011 : Type'} (f : type686 _105011) (_50042 : _105011 -> Prop) (p1 : _105011) : (term274 _105011 p1 f _50042) = (term278 _105011 f _50042 p1).
Proof. exact (@lem4380193 (term240 _105011 f _50042) (@I (_105011 -> Prop) _50042 p1)). Qed.
Lemma lem4380196 (a : Prop) : (term87 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4380197 {_105011 : Type'} (f : type686 _105011) (_50042 : _105011 -> Prop) : (term279 _105011 f _50042) = (@I ((_105011 -> Prop) -> Prop) f _50042).
Proof. exact (@lem4380196 (@I ((_105011 -> Prop) -> Prop) f _50042)). Qed.
Lemma lem4380198 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4380199 {_105011 : Type'} (f : type686 _105011) (_50042 : _105011 -> Prop) : (term280 _105011 f _50042) = (term281 _105011 f _50042).
Proof. exact (MK_COMB (@lem4380198) (@lem4380197 _105011 f _50042)). Qed.
Lemma lem4380200 {_105011 : Type'} (_50042 : _105011 -> Prop) (p1 : _105011) : (@I (_105011 -> Prop) _50042 p1) = (@I (_105011 -> Prop) _50042 p1).
Proof. exact (eq_refl (@I (_105011 -> Prop) _50042 p1)). Qed.
Lemma lem4380201 {_105011 : Type'} (f : type686 _105011) (_50042 : _105011 -> Prop) (p1 : _105011) : (term278 _105011 f _50042 p1) = (term282 _105011 f _50042 p1).
Proof. exact (MK_COMB (@lem4380199 _105011 f _50042) (@lem4380200 _105011 _50042 p1)). Qed.
Lemma lem4380202 {_105011 : Type'} (f : type686 _105011) (_50042 : _105011 -> Prop) (p1 : _105011) : (term274 _105011 p1 f _50042) = (term282 _105011 f _50042 p1).
Proof. exact (TRANS (@lem4380194 _105011 f _50042 p1) (@lem4380201 _105011 f _50042 p1)). Qed.
Lemma lem4380205 {_105011 _105012 : Type'} (_50042 : _105011 -> Prop) (f : type686 _105011) (s : _105011 -> Prop) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) (h1 : term263 _105011 _105012 f s p1 t p2) : term282 _105011 f _50042 p1.
Proof. exact (EQ_MP (@lem4380202 _105011 f _50042 p1) (@lem4380191 _105011 _105012 _50042 f s p1 t p2 h1)). Qed.
Lemma lem4380206 {_105011 _105012 : Type'} (_50042 : _105011 -> Prop) (f : type686 _105011) (s : _105011 -> Prop) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) (h1 : term263 _105011 _105012 f s p1 t p2) : term282 _105011 f _50042 p1.
Proof. exact (@lem4380205 _105011 _105012 _50042 f s p1 t p2 h1). Qed.
Lemma lem4380207 {_105011 _105012 : Type'} (f : type686 _105011) (s : _105011 -> Prop) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) (h1 : term263 _105011 _105012 f s p1 t p2) : term282 _105011 f s p1.
Proof. exact (@lem4380206 _105011 _105012 s f s p1 t p2 h1). Qed.
Lemma lem4380210 {_105011 _105012 : Type'} (f : type686 _105011) (s : _105011 -> Prop) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) (h1 : term263 _105011 _105012 f s p1 t p2) : @I (_105011 -> Prop) s p1.
Proof. exact (@lem4380207 _105011 _105012 f s p1 t p2 h1 (@lem4380162 _105011 _105012 f s p1 t p2 h1)). Qed.
Lemma lem4380211 {_105011 _105012 : Type'} (f : type686 _105011) (s : _105011 -> Prop) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) (h1 : term263 _105011 _105012 f s p1 t p2) : term283 _105011 s p1.
Proof. exact (fun h0 : term246 _105011 s p1 => @lem4380210 _105011 _105012 f s p1 t p2 h1). Qed.
Lemma lem4380213 (p : Prop) : (term273 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4380214 {_105011 : Type'} (s : _105011 -> Prop) (p1 : _105011) : (term283 _105011 s p1) = (@I (_105011 -> Prop) s p1).
Proof. exact (@lem4380213 (@I (_105011 -> Prop) s p1)). Qed.
Lemma lem4380215 {_105011 _105012 : Type'} (f : type686 _105011) (s : _105011 -> Prop) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) (h1 : term263 _105011 _105012 f s p1 t p2) : @I (_105011 -> Prop) s p1.
Proof. exact (EQ_MP (@lem4380214 _105011 s p1) (@lem4380211 _105011 _105012 f s p1 t p2 h1)). Qed.
Lemma lem4380218 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4380220 {_105011 : Type'} (s : _105011 -> Prop) (p1 : _105011) : (term246 _105011 s p1) = (term284 _105011 s p1).
Proof. exact (@lem4380218 (@I (_105011 -> Prop) s p1)). Qed.
Lemma lem4380223 {_105011 : Type'} (s : _105011 -> Prop) (p1 : _105011) (h1 : term246 _105011 s p1) : term284 _105011 s p1.
Proof. exact (EQ_MP (@lem4380220 _105011 s p1) (@lem4380107 _105011 s p1 h1)). Qed.
Lemma lem4380226 {_105011 _105012 : Type'} (f : type686 _105011) (s : _105011 -> Prop) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) (h1 : term246 _105011 s p1) (h2 : term263 _105011 _105012 f s p1 t p2) : False.
Proof. exact (@lem4380223 _105011 s p1 h1 (@lem4380215 _105011 _105012 f s p1 t p2 h2)). Qed.
Lemma lem4380227 {_105011 _105012 : Type'} (f : type686 _105011) (s : _105011 -> Prop) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) (h1 : term246 _105011 s p1) (h2 : term263 _105011 _105012 f s p1 t p2) : term285.
Proof. exact (fun h0 : ~ False => @lem4380226 _105011 _105012 f s p1 t p2 h1 h2). Qed.
Lemma lem4380229 (p : Prop) : (term273 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4380230 : term285 = False.
Proof. exact (@lem4380229 False). Qed.
Lemma lem4380231 {_105011 _105012 : Type'} (f : type686 _105011) (s : _105011 -> Prop) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) (h1 : term246 _105011 s p1) (h2 : term263 _105011 _105012 f s p1 t p2) : False.
Proof. exact (EQ_MP (@lem4380230) (@lem4380227 _105011 _105012 f s p1 t p2 h1 h2)). Qed.
Lemma lem4380233 {_105011 _105012 : Type'} (f : type686 _105011) (s : _105011 -> Prop) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) (h1 : term263 _105011 _105012 f s p1 t p2) : @I (_105012 -> Prop) t p2.
Proof. exact (proj2 (@lem4379941 _105011 _105012 f s p1 t p2 h1)). Qed.
Lemma lem4380234 {_105011 _105012 : Type'} (f : type686 _105011) (s : _105011 -> Prop) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) (h1 : term263 _105011 _105012 f s p1 t p2) : term283 _105012 t p2.
Proof. exact (fun h0 : term246 _105012 t p2 => @lem4380233 _105011 _105012 f s p1 t p2 h1). Qed.
Lemma lem4380236 (p : Prop) : (term273 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4380237 {_105012 : Type'} (t : _105012 -> Prop) (p2 : _105012) : (term283 _105012 t p2) = (@I (_105012 -> Prop) t p2).
Proof. exact (@lem4380236 (@I (_105012 -> Prop) t p2)). Qed.
Lemma lem4380238 {_105011 _105012 : Type'} (f : type686 _105011) (s : _105011 -> Prop) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) (h1 : term263 _105011 _105012 f s p1 t p2) : @I (_105012 -> Prop) t p2.
Proof. exact (EQ_MP (@lem4380237 _105012 t p2) (@lem4380234 _105011 _105012 f s p1 t p2 h1)). Qed.
Lemma lem4380241 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4380243 {_105012 : Type'} (t : _105012 -> Prop) (p2 : _105012) : (term246 _105012 t p2) = (term284 _105012 t p2).
Proof. exact (@lem4380241 (@I (_105012 -> Prop) t p2)). Qed.
Lemma lem4380246 {_105012 : Type'} (t : _105012 -> Prop) (p2 : _105012) (h1 : term246 _105012 t p2) : term284 _105012 t p2.
Proof. exact (EQ_MP (@lem4380243 _105012 t p2) (@lem4380121 _105012 t p2 h1)). Qed.
Lemma lem4380249 {_105011 _105012 : Type'} (f : type686 _105011) (s : _105011 -> Prop) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) (h1 : term246 _105012 t p2) (h2 : term263 _105011 _105012 f s p1 t p2) : False.
Proof. exact (@lem4380246 _105012 t p2 h1 (@lem4380238 _105011 _105012 f s p1 t p2 h2)). Qed.
Lemma lem4380250 {_105011 _105012 : Type'} (f : type686 _105011) (s : _105011 -> Prop) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) (h1 : term246 _105012 t p2) (h2 : term263 _105011 _105012 f s p1 t p2) : term285.
Proof. exact (fun h0 : ~ False => @lem4380249 _105011 _105012 f s p1 t p2 h1 h2). Qed.
Lemma lem4380252 (p : Prop) : (term273 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4380253 : term285 = False.
Proof. exact (@lem4380252 False). Qed.
Lemma lem4380254 {_105011 _105012 : Type'} (f : type686 _105011) (s : _105011 -> Prop) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) (h1 : term246 _105012 t p2) (h2 : term263 _105011 _105012 f s p1 t p2) : False.
Proof. exact (EQ_MP (@lem4380253) (@lem4380250 _105011 _105012 f s p1 t p2 h1 h2)). Qed.
Lemma lem4380256 {_105011 : Type'} (f : type686 _105011) (s : _105011 -> Prop) (p1 : _105011) (h1 : term248 _105011 f s p1) : @I ((_105011 -> Prop) -> Prop) f s.
Proof. exact (proj1 (@lem4379950 _105011 f s p1 h1)). Qed.
Lemma lem4380257 {_105011 : Type'} (f : type686 _105011) (s : _105011 -> Prop) (p1 : _105011) (h1 : term248 _105011 f s p1) : term272 _105011 f s.
Proof. exact (fun h0 : term240 _105011 f s => @lem4380256 _105011 f s p1 h1). Qed.
Lemma lem4380259 (p : Prop) : (term273 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4380260 {_105011 : Type'} (f : type686 _105011) (s : _105011 -> Prop) : (term272 _105011 f s) = (@I ((_105011 -> Prop) -> Prop) f s).
Proof. exact (@lem4380259 (@I ((_105011 -> Prop) -> Prop) f s)). Qed.
Lemma lem4380261 {_105011 : Type'} (f : type686 _105011) (s : _105011 -> Prop) (p1 : _105011) (h1 : term248 _105011 f s p1) : @I ((_105011 -> Prop) -> Prop) f s.
Proof. exact (EQ_MP (@lem4380260 _105011 f s) (@lem4380257 _105011 f s p1 h1)). Qed.
Lemma lem4380267 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4380268 {_105011 : Type'} (p1 : _105011) (f : type686 _105011) (_50044 : _105011 -> Prop) : (term257 _105011 f _50044 p1) = (term274 _105011 p1 f _50044).
Proof. exact (@lem4380267 (@I (_105011 -> Prop) _50044 p1) (term240 _105011 f _50044)). Qed.
Lemma lem4380274 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4380275 {_105011 : Type'} (p1 : _105011) (f : type686 _105011) (_50044 : _105011 -> Prop) : (term275 _105011 f _50044 p1) = (term276 _105011 p1 f _50044).
Proof. exact (MK_COMB (@lem4380274) (@lem4380268 _105011 p1 f _50044)). Qed.
Lemma lem4380281 {_105011 : Type'} (p1 : _105011) (f : type686 _105011) (_50044 : _105011 -> Prop) : (term274 _105011 p1 f _50044) = (term274 _105011 p1 f _50044).
Proof. exact (eq_refl (term274 _105011 p1 f _50044)). Qed.
Lemma lem4380282 {_105011 : Type'} (p1 : _105011) (f : type686 _105011) (_50044 : _105011 -> Prop) : ((term257 _105011 f _50044 p1) = (term274 _105011 p1 f _50044)) = ((term274 _105011 p1 f _50044) = (term274 _105011 p1 f _50044)).
Proof. exact (MK_COMB (@lem4380275 _105011 p1 f _50044) (@lem4380281 _105011 p1 f _50044)). Qed.
Lemma lem4380284 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4380285 (x : Prop) : (x = x) = True.
Proof. exact (@lem4380284 Prop x). Qed.
Lemma lem4380286 {_105011 : Type'} (p1 : _105011) (f : type686 _105011) (_50044 : _105011 -> Prop) : ((term274 _105011 p1 f _50044) = (term274 _105011 p1 f _50044)) = True.
Proof. exact (@lem4380285 (term274 _105011 p1 f _50044)). Qed.
Lemma lem4380287 {_105011 : Type'} (p1 : _105011) (f : type686 _105011) (_50044 : _105011 -> Prop) : ((term257 _105011 f _50044 p1) = (term274 _105011 p1 f _50044)) = True.
Proof. exact (TRANS (@lem4380282 _105011 p1 f _50044) (@lem4380286 _105011 p1 f _50044)). Qed.
Lemma lem4380288 {_105011 : Type'} (p1 : _105011) (f : type686 _105011) (_50044 : _105011 -> Prop) : True = ((term257 _105011 f _50044 p1) = (term274 _105011 p1 f _50044)).
Proof. exact (SYM (@lem4380287 _105011 p1 f _50044)). Qed.
Lemma lem4380289 {_105011 : Type'} (p1 : _105011) (f : type686 _105011) (_50044 : _105011 -> Prop) : (term257 _105011 f _50044 p1) = (term274 _105011 p1 f _50044).
Proof. exact (EQ_MP (@lem4380288 _105011 p1 f _50044) (@lem0)). Qed.
Lemma lem4380290 {_105011 _105012 : Type'} (_50044 : _105011 -> Prop) (s : _105011 -> Prop) (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) (h1 : term252 _105011 _105012 s f p1 t p2) : term274 _105011 p1 f _50044.
Proof. exact (EQ_MP (@lem4380289 _105011 p1 f _50044) (@lem4380133 _105011 _105012 _50044 s f p1 t p2 h1)). Qed.
Lemma lem4380292 (b : Prop) (a : Prop) : (a \/ b) = (term277 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4380293 {_105011 : Type'} (f : type686 _105011) (_50044 : _105011 -> Prop) (p1 : _105011) : (term274 _105011 p1 f _50044) = (term278 _105011 f _50044 p1).
Proof. exact (@lem4380292 (term240 _105011 f _50044) (@I (_105011 -> Prop) _50044 p1)). Qed.
Lemma lem4380295 (a : Prop) : (term87 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4380296 {_105011 : Type'} (f : type686 _105011) (_50044 : _105011 -> Prop) : (term279 _105011 f _50044) = (@I ((_105011 -> Prop) -> Prop) f _50044).
Proof. exact (@lem4380295 (@I ((_105011 -> Prop) -> Prop) f _50044)). Qed.
Lemma lem4380297 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4380298 {_105011 : Type'} (f : type686 _105011) (_50044 : _105011 -> Prop) : (term280 _105011 f _50044) = (term281 _105011 f _50044).
Proof. exact (MK_COMB (@lem4380297) (@lem4380296 _105011 f _50044)). Qed.
Lemma lem4380299 {_105011 : Type'} (_50044 : _105011 -> Prop) (p1 : _105011) : (@I (_105011 -> Prop) _50044 p1) = (@I (_105011 -> Prop) _50044 p1).
Proof. exact (eq_refl (@I (_105011 -> Prop) _50044 p1)). Qed.
Lemma lem4380300 {_105011 : Type'} (f : type686 _105011) (_50044 : _105011 -> Prop) (p1 : _105011) : (term278 _105011 f _50044 p1) = (term282 _105011 f _50044 p1).
Proof. exact (MK_COMB (@lem4380298 _105011 f _50044) (@lem4380299 _105011 _50044 p1)). Qed.
Lemma lem4380301 {_105011 : Type'} (f : type686 _105011) (_50044 : _105011 -> Prop) (p1 : _105011) : (term274 _105011 p1 f _50044) = (term282 _105011 f _50044 p1).
Proof. exact (TRANS (@lem4380293 _105011 f _50044 p1) (@lem4380300 _105011 f _50044 p1)). Qed.
Lemma lem4380304 {_105011 _105012 : Type'} (_50044 : _105011 -> Prop) (s : _105011 -> Prop) (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) (h1 : term252 _105011 _105012 s f p1 t p2) : term282 _105011 f _50044 p1.
Proof. exact (EQ_MP (@lem4380301 _105011 f _50044 p1) (@lem4380290 _105011 _105012 _50044 s f p1 t p2 h1)). Qed.
Lemma lem4380305 {_105011 _105012 : Type'} (_50044 : _105011 -> Prop) (s : _105011 -> Prop) (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) (h1 : term252 _105011 _105012 s f p1 t p2) : term282 _105011 f _50044 p1.
Proof. exact (@lem4380304 _105011 _105012 _50044 s f p1 t p2 h1). Qed.
Lemma lem4380306 {_105011 _105012 : Type'} (s : _105011 -> Prop) (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) (h1 : term252 _105011 _105012 s f p1 t p2) : term282 _105011 f s p1.
Proof. exact (@lem4380305 _105011 _105012 s s f p1 t p2 h1). Qed.
Lemma lem4380309 {_105011 _105012 : Type'} (s : _105011 -> Prop) (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) (h1 : term248 _105011 f s p1) (h2 : term252 _105011 _105012 s f p1 t p2) : @I (_105011 -> Prop) s p1.
Proof. exact (@lem4380306 _105011 _105012 s f p1 t p2 h2 (@lem4380261 _105011 f s p1 h1)). Qed.
Lemma lem4380310 {_105011 _105012 : Type'} (s : _105011 -> Prop) (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) (h1 : term248 _105011 f s p1) (h2 : term252 _105011 _105012 s f p1 t p2) : term283 _105011 s p1.
Proof. exact (fun h0 : term246 _105011 s p1 => @lem4380309 _105011 _105012 s f p1 t p2 h1 h2). Qed.
Lemma lem4380312 (p : Prop) : (term273 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4380313 {_105011 : Type'} (s : _105011 -> Prop) (p1 : _105011) : (term283 _105011 s p1) = (@I (_105011 -> Prop) s p1).
Proof. exact (@lem4380312 (@I (_105011 -> Prop) s p1)). Qed.
Lemma lem4380314 {_105011 _105012 : Type'} (s : _105011 -> Prop) (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) (h1 : term248 _105011 f s p1) (h2 : term252 _105011 _105012 s f p1 t p2) : @I (_105011 -> Prop) s p1.
Proof. exact (EQ_MP (@lem4380313 _105011 s p1) (@lem4380310 _105011 _105012 s f p1 t p2 h1 h2)). Qed.
Lemma lem4380317 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4380319 {_105011 : Type'} (s : _105011 -> Prop) (p1 : _105011) : (term246 _105011 s p1) = (term284 _105011 s p1).
Proof. exact (@lem4380317 (@I (_105011 -> Prop) s p1)). Qed.
Lemma lem4380322 {_105011 : Type'} (f : type686 _105011) (s : _105011 -> Prop) (p1 : _105011) (h1 : term248 _105011 f s p1) : term284 _105011 s p1.
Proof. exact (EQ_MP (@lem4380319 _105011 s p1) (@lem4380127 _105011 f s p1 h1)). Qed.
Lemma lem4380325 {_105011 _105012 : Type'} (s : _105011 -> Prop) (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) (h1 : term248 _105011 f s p1) (h2 : term252 _105011 _105012 s f p1 t p2) : False.
Proof. exact (@lem4380322 _105011 f s p1 h1 (@lem4380314 _105011 _105012 s f p1 t p2 h1 h2)). Qed.
Lemma lem4380326 {_105011 _105012 : Type'} (s : _105011 -> Prop) (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) (h1 : term248 _105011 f s p1) (h2 : term252 _105011 _105012 s f p1 t p2) : term285.
Proof. exact (fun h0 : ~ False => @lem4380325 _105011 _105012 s f p1 t p2 h1 h2). Qed.
Lemma lem4380328 (p : Prop) : (term273 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4380329 : term285 = False.
Proof. exact (@lem4380328 False). Qed.
Lemma lem4380330 {_105011 _105012 : Type'} (s : _105011 -> Prop) (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) (h1 : term248 _105011 f s p1) (h2 : term252 _105011 _105012 s f p1 t p2) : False.
Proof. exact (EQ_MP (@lem4380329) (@lem4380326 _105011 _105012 s f p1 t p2 h1 h2)). Qed.
Lemma lem4380332 {_105011 : Type'} (f : type686 _105011) (x : _105011 -> Prop) (h1 : f x) : @I ((_105011 -> Prop) -> Prop) f x.
Proof. exact (EQ_MP (@lem4379936 _105011 f x) (@lem4379781 _105011 f x h1)). Qed.
Lemma lem4380333 {_105011 : Type'} (f : type686 _105011) (x : _105011 -> Prop) (h1 : f x) : term272 _105011 f x.
Proof. exact (fun h0 : term240 _105011 f x => @lem4380332 _105011 f x h1). Qed.
Lemma lem4380335 (p : Prop) : (term273 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4380336 {_105011 : Type'} (f : type686 _105011) (x : _105011 -> Prop) : (term272 _105011 f x) = (@I ((_105011 -> Prop) -> Prop) f x).
Proof. exact (@lem4380335 (@I ((_105011 -> Prop) -> Prop) f x)). Qed.
Lemma lem4380337 {_105011 : Type'} (f : type686 _105011) (x : _105011 -> Prop) (h1 : f x) : @I ((_105011 -> Prop) -> Prop) f x.
Proof. exact (EQ_MP (@lem4380336 _105011 f x) (@lem4380333 _105011 f x h1)). Qed.
Lemma lem4380343 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4380344 {_105011 _105012 : Type'} (t : _105012 -> Prop) (p2 : _105012) (f : type686 _105011) (_50045 : _105011 -> Prop) : (term271 _105011 _105012 f _50045 t p2) = (term286 _105011 _105012 t p2 f _50045).
Proof. exact (@lem4380343 (@I (_105012 -> Prop) t p2) (term240 _105011 f _50045)). Qed.
Lemma lem4380350 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4380351 {_105011 _105012 : Type'} (t : _105012 -> Prop) (p2 : _105012) (f : type686 _105011) (_50045 : _105011 -> Prop) : (term287 _105011 _105012 f _50045 t p2) = (term288 _105011 _105012 t p2 f _50045).
Proof. exact (MK_COMB (@lem4380350) (@lem4380344 _105011 _105012 t p2 f _50045)). Qed.
Lemma lem4380357 {_105011 _105012 : Type'} (t : _105012 -> Prop) (p2 : _105012) (f : type686 _105011) (_50045 : _105011 -> Prop) : (term286 _105011 _105012 t p2 f _50045) = (term286 _105011 _105012 t p2 f _50045).
Proof. exact (eq_refl (term286 _105011 _105012 t p2 f _50045)). Qed.
Lemma lem4380358 {_105011 _105012 : Type'} (t : _105012 -> Prop) (p2 : _105012) (f : type686 _105011) (_50045 : _105011 -> Prop) : ((term271 _105011 _105012 f _50045 t p2) = (term286 _105011 _105012 t p2 f _50045)) = ((term286 _105011 _105012 t p2 f _50045) = (term286 _105011 _105012 t p2 f _50045)).
Proof. exact (MK_COMB (@lem4380351 _105011 _105012 t p2 f _50045) (@lem4380357 _105011 _105012 t p2 f _50045)). Qed.
Lemma lem4380360 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4380361 (x : Prop) : (x = x) = True.
Proof. exact (@lem4380360 Prop x). Qed.
Lemma lem4380362 {_105011 _105012 : Type'} (t : _105012 -> Prop) (p2 : _105012) (f : type686 _105011) (_50045 : _105011 -> Prop) : ((term286 _105011 _105012 t p2 f _50045) = (term286 _105011 _105012 t p2 f _50045)) = True.
Proof. exact (@lem4380361 (term286 _105011 _105012 t p2 f _50045)). Qed.
Lemma lem4380363 {_105011 _105012 : Type'} (t : _105012 -> Prop) (p2 : _105012) (f : type686 _105011) (_50045 : _105011 -> Prop) : ((term271 _105011 _105012 f _50045 t p2) = (term286 _105011 _105012 t p2 f _50045)) = True.
Proof. exact (TRANS (@lem4380358 _105011 _105012 t p2 f _50045) (@lem4380362 _105011 _105012 t p2 f _50045)). Qed.
Lemma lem4380364 {_105011 _105012 : Type'} (t : _105012 -> Prop) (p2 : _105012) (f : type686 _105011) (_50045 : _105011 -> Prop) : True = ((term271 _105011 _105012 f _50045 t p2) = (term286 _105011 _105012 t p2 f _50045)).
Proof. exact (SYM (@lem4380363 _105011 _105012 t p2 f _50045)). Qed.
Lemma lem4380365 {_105011 _105012 : Type'} (t : _105012 -> Prop) (p2 : _105012) (f : type686 _105011) (_50045 : _105011 -> Prop) : (term271 _105011 _105012 f _50045 t p2) = (term286 _105011 _105012 t p2 f _50045).
Proof. exact (EQ_MP (@lem4380364 _105011 _105012 t p2 f _50045) (@lem0)). Qed.
Lemma lem4380366 {_105011 _105012 : Type'} (_50045 : _105011 -> Prop) (s : _105011 -> Prop) (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) (h1 : term252 _105011 _105012 s f p1 t p2) : term286 _105011 _105012 t p2 f _50045.
Proof. exact (EQ_MP (@lem4380365 _105011 _105012 t p2 f _50045) (@lem4380155 _105011 _105012 _50045 s f p1 t p2 h1)). Qed.
Lemma lem4380368 (b : Prop) (a : Prop) : (a \/ b) = (term277 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4380369 {_105011 _105012 : Type'} (f : type686 _105011) (_50045 : _105011 -> Prop) (t : _105012 -> Prop) (p2 : _105012) : (term286 _105011 _105012 t p2 f _50045) = (term289 _105011 _105012 f _50045 t p2).
Proof. exact (@lem4380368 (term240 _105011 f _50045) (@I (_105012 -> Prop) t p2)). Qed.
Lemma lem4380371 (a : Prop) : (term87 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4380372 {_105011 : Type'} (f : type686 _105011) (_50045 : _105011 -> Prop) : (term279 _105011 f _50045) = (@I ((_105011 -> Prop) -> Prop) f _50045).
Proof. exact (@lem4380371 (@I ((_105011 -> Prop) -> Prop) f _50045)). Qed.
Lemma lem4380373 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4380374 {_105011 : Type'} (f : type686 _105011) (_50045 : _105011 -> Prop) : (term280 _105011 f _50045) = (term281 _105011 f _50045).
Proof. exact (MK_COMB (@lem4380373) (@lem4380372 _105011 f _50045)). Qed.
Lemma lem4380375 {_105012 : Type'} (t : _105012 -> Prop) (p2 : _105012) : (@I (_105012 -> Prop) t p2) = (@I (_105012 -> Prop) t p2).
Proof. exact (eq_refl (@I (_105012 -> Prop) t p2)). Qed.
Lemma lem4380376 {_105011 _105012 : Type'} (f : type686 _105011) (_50045 : _105011 -> Prop) (t : _105012 -> Prop) (p2 : _105012) : (term289 _105011 _105012 f _50045 t p2) = (term290 _105011 _105012 f _50045 t p2).
Proof. exact (MK_COMB (@lem4380374 _105011 f _50045) (@lem4380375 _105012 t p2)). Qed.
Lemma lem4380377 {_105011 _105012 : Type'} (f : type686 _105011) (_50045 : _105011 -> Prop) (t : _105012 -> Prop) (p2 : _105012) : (term286 _105011 _105012 t p2 f _50045) = (term290 _105011 _105012 f _50045 t p2).
Proof. exact (TRANS (@lem4380369 _105011 _105012 f _50045 t p2) (@lem4380376 _105011 _105012 f _50045 t p2)). Qed.
Lemma lem4380380 {_105011 _105012 : Type'} (_50045 : _105011 -> Prop) (s : _105011 -> Prop) (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) (h1 : term252 _105011 _105012 s f p1 t p2) : term290 _105011 _105012 f _50045 t p2.
Proof. exact (EQ_MP (@lem4380377 _105011 _105012 f _50045 t p2) (@lem4380366 _105011 _105012 _50045 s f p1 t p2 h1)). Qed.
Lemma lem4380381 {_105011 _105012 : Type'} (_50045 : _105011 -> Prop) (s : _105011 -> Prop) (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) (h1 : term252 _105011 _105012 s f p1 t p2) : term290 _105011 _105012 f _50045 t p2.
Proof. exact (@lem4380380 _105011 _105012 _50045 s f p1 t p2 h1). Qed.
Lemma lem4380382 {_105011 _105012 : Type'} (x : _105011 -> Prop) (s : _105011 -> Prop) (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) (h1 : term252 _105011 _105012 s f p1 t p2) : term290 _105011 _105012 f x t p2.
Proof. exact (@lem4380381 _105011 _105012 x s f p1 t p2 h1). Qed.
Lemma lem4380385 {_105011 _105012 : Type'} (x : _105011 -> Prop) (s : _105011 -> Prop) (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) (h1 : f x) (h2 : term252 _105011 _105012 s f p1 t p2) : @I (_105012 -> Prop) t p2.
Proof. exact (@lem4380382 _105011 _105012 x s f p1 t p2 h2 (@lem4380337 _105011 f x h1)). Qed.
Lemma lem4380386 {_105011 _105012 : Type'} (x : _105011 -> Prop) (s : _105011 -> Prop) (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) (h1 : f x) (h2 : term252 _105011 _105012 s f p1 t p2) : term283 _105012 t p2.
Proof. exact (fun h0 : term246 _105012 t p2 => @lem4380385 _105011 _105012 x s f p1 t p2 h1 h2). Qed.
Lemma lem4380388 (p : Prop) : (term273 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4380389 {_105012 : Type'} (t : _105012 -> Prop) (p2 : _105012) : (term283 _105012 t p2) = (@I (_105012 -> Prop) t p2).
Proof. exact (@lem4380388 (@I (_105012 -> Prop) t p2)). Qed.
Lemma lem4380390 {_105011 _105012 : Type'} (x : _105011 -> Prop) (s : _105011 -> Prop) (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) (h1 : f x) (h2 : term252 _105011 _105012 s f p1 t p2) : @I (_105012 -> Prop) t p2.
Proof. exact (EQ_MP (@lem4380389 _105012 t p2) (@lem4380386 _105011 _105012 x s f p1 t p2 h1 h2)). Qed.
Lemma lem4380393 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4380395 {_105012 : Type'} (t : _105012 -> Prop) (p2 : _105012) : (term246 _105012 t p2) = (term284 _105012 t p2).
Proof. exact (@lem4380393 (@I (_105012 -> Prop) t p2)). Qed.
Lemma lem4380398 {_105012 : Type'} (t : _105012 -> Prop) (p2 : _105012) (h1 : term246 _105012 t p2) : term284 _105012 t p2.
Proof. exact (EQ_MP (@lem4380395 _105012 t p2) (@lem4380143 _105012 t p2 h1)). Qed.
Lemma lem4380401 {_105011 _105012 : Type'} (x : _105011 -> Prop) (s : _105011 -> Prop) (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) (h1 : term246 _105012 t p2) (h2 : f x) (h3 : term252 _105011 _105012 s f p1 t p2) : False.
Proof. exact (@lem4380398 _105012 t p2 h1 (@lem4380390 _105011 _105012 x s f p1 t p2 h2 h3)). Qed.
Lemma lem4380402 {_105011 _105012 : Type'} (x : _105011 -> Prop) (s : _105011 -> Prop) (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) (h1 : term246 _105012 t p2) (h2 : f x) (h3 : term252 _105011 _105012 s f p1 t p2) : term285.
Proof. exact (fun h0 : ~ False => @lem4380401 _105011 _105012 x s f p1 t p2 h1 h2 h3). Qed.
Lemma lem4380404 (p : Prop) : (term273 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4380405 : term285 = False.
Proof. exact (@lem4380404 False). Qed.
Lemma lem4380406 {_105011 _105012 : Type'} (x : _105011 -> Prop) (s : _105011 -> Prop) (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) (h1 : term246 _105012 t p2) (h2 : f x) (h3 : term252 _105011 _105012 s f p1 t p2) : False.
Proof. exact (EQ_MP (@lem4380405) (@lem4380402 _105011 _105012 x s f p1 t p2 h1 h2 h3)). Qed.
Lemma lem4380407 {_105011 _105012 : Type'} (x : _105011 -> Prop) (s : _105011 -> Prop) (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) (h1 : term246 _105012 t p2) (h2 : f x) (h3 : term252 _105011 _105012 s f p1 t p2) : (term246 _105012 t p2) = False.
Proof. exact (prop_ext (fun h4 : term246 _105012 t p2 => @lem4380406 _105011 _105012 x s f p1 t p2 h1 h2 h3) (fun h4 : False => @lem4380143 _105012 t p2 h1)). Qed.
Lemma lem4380408 {_105011 _105012 : Type'} (x : _105011 -> Prop) (s : _105011 -> Prop) (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) (h1 : term246 _105012 t p2) (h2 : f x) (h3 : term252 _105011 _105012 s f p1 t p2) : False.
Proof. exact (EQ_MP (@lem4380407 _105011 _105012 x s f p1 t p2 h1 h2 h3) (@lem4380143 _105012 t p2 h1)). Qed.
Lemma lem4380409 {_105011 _105012 : Type'} (f : type686 _105011) (s : _105011 -> Prop) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) (h1 : term246 _105012 t p2) (h2 : term263 _105011 _105012 f s p1 t p2) : (term246 _105012 t p2) = False.
Proof. exact (prop_ext (fun h3 : term246 _105012 t p2 => @lem4380254 _105011 _105012 f s p1 t p2 h1 h2) (fun h3 : False => @lem4380121 _105012 t p2 h1)). Qed.
Lemma lem4380410 {_105011 _105012 : Type'} (f : type686 _105011) (s : _105011 -> Prop) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) (h1 : term246 _105012 t p2) (h2 : term263 _105011 _105012 f s p1 t p2) : False.
Proof. exact (EQ_MP (@lem4380409 _105011 _105012 f s p1 t p2 h1 h2) (@lem4380121 _105012 t p2 h1)). Qed.
Lemma lem4380411 {_105011 _105012 : Type'} (f : type686 _105011) (s : _105011 -> Prop) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) (h1 : term246 _105011 s p1) (h2 : term263 _105011 _105012 f s p1 t p2) : (term246 _105011 s p1) = False.
Proof. exact (prop_ext (fun h3 : term246 _105011 s p1 => @lem4380231 _105011 _105012 f s p1 t p2 h1 h2) (fun h3 : False => @lem4380107 _105011 s p1 h1)). Qed.
Lemma lem4380412 {_105011 _105012 : Type'} (f : type686 _105011) (s : _105011 -> Prop) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) (h1 : term246 _105011 s p1) (h2 : term263 _105011 _105012 f s p1 t p2) : False.
Proof. exact (EQ_MP (@lem4380411 _105011 _105012 f s p1 t p2 h1 h2) (@lem4380107 _105011 s p1 h1)). Qed.
Lemma lem4380413 {_105011 _105012 : Type'} (x : _105011 -> Prop) (s : _105011 -> Prop) (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) (h1 : term246 _105012 t p2) (h2 : f x) (h3 : term252 _105011 _105012 s f p1 t p2) : (term246 _105012 t p2) = False.
Proof. exact (prop_ext (fun h4 : term246 _105012 t p2 => @lem4380408 _105011 _105012 x s f p1 t p2 h1 h2 h3) (fun h4 : False => @lem4380077 _105012 t p2 h1)). Qed.
Lemma lem4380414 {_105011 _105012 : Type'} (x : _105011 -> Prop) (s : _105011 -> Prop) (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) (h1 : term246 _105012 t p2) (h2 : f x) (h3 : term252 _105011 _105012 s f p1 t p2) : False.
Proof. exact (EQ_MP (@lem4380413 _105011 _105012 x s f p1 t p2 h1 h2 h3) (@lem4380077 _105012 t p2 h1)). Qed.
Lemma lem4380415 {_105011 _105012 : Type'} (f : type686 _105011) (s : _105011 -> Prop) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) (h1 : term246 _105012 t p2) (h2 : term263 _105011 _105012 f s p1 t p2) : (term246 _105012 t p2) = False.
Proof. exact (prop_ext (fun h3 : term246 _105012 t p2 => @lem4380410 _105011 _105012 f s p1 t p2 h1 h2) (fun h3 : False => @lem4380011 _105012 t p2 h1)). Qed.
Lemma lem4380416 {_105011 _105012 : Type'} (f : type686 _105011) (s : _105011 -> Prop) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) (h1 : term246 _105012 t p2) (h2 : term263 _105011 _105012 f s p1 t p2) : False.
Proof. exact (EQ_MP (@lem4380415 _105011 _105012 f s p1 t p2 h1 h2) (@lem4380011 _105012 t p2 h1)). Qed.
Lemma lem4380417 {_105011 _105012 : Type'} (f : type686 _105011) (s : _105011 -> Prop) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) (h1 : term246 _105011 s p1) (h2 : term263 _105011 _105012 f s p1 t p2) : (term246 _105011 s p1) = False.
Proof. exact (prop_ext (fun h3 : term246 _105011 s p1 => @lem4380412 _105011 _105012 f s p1 t p2 h1 h2) (fun h3 : False => @lem4379982 _105011 s p1 h1)). Qed.
Lemma lem4380418 {_105011 _105012 : Type'} (f : type686 _105011) (s : _105011 -> Prop) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) (h1 : term246 _105011 s p1) (h2 : term263 _105011 _105012 f s p1 t p2) : False.
Proof. exact (EQ_MP (@lem4380417 _105011 _105012 f s p1 t p2 h1 h2) (@lem4379982 _105011 s p1 h1)). Qed.
Lemma lem4380419 {_105011 _105012 : Type'} (x : _105011 -> Prop) (s : _105011 -> Prop) (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) (h1 : term246 _105012 t p2) (h2 : f x) (h3 : term252 _105011 _105012 s f p1 t p2) : (term246 _105012 t p2) = False.
Proof. exact (prop_ext (fun h4 : term246 _105012 t p2 => @lem4380414 _105011 _105012 x s f p1 t p2 h1 h2 h3) (fun h4 : False => @lem4380077 _105012 t p2 h1)). Qed.
Lemma lem4380420 {_105011 _105012 : Type'} (x : _105011 -> Prop) (s : _105011 -> Prop) (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) (h1 : term246 _105012 t p2) (h2 : f x) (h3 : term252 _105011 _105012 s f p1 t p2) : False.
Proof. exact (EQ_MP (@lem4380419 _105011 _105012 x s f p1 t p2 h1 h2 h3) (@lem4380077 _105012 t p2 h1)). Qed.
Lemma lem4380421 {_105011 _105012 : Type'} (f : type686 _105011) (s : _105011 -> Prop) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) (h1 : term246 _105012 t p2) (h2 : term263 _105011 _105012 f s p1 t p2) : (term246 _105012 t p2) = False.
Proof. exact (prop_ext (fun h3 : term246 _105012 t p2 => @lem4380416 _105011 _105012 f s p1 t p2 h1 h2) (fun h3 : False => @lem4380011 _105012 t p2 h1)). Qed.
Lemma lem4380422 {_105011 _105012 : Type'} (f : type686 _105011) (s : _105011 -> Prop) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) (h1 : term246 _105012 t p2) (h2 : term263 _105011 _105012 f s p1 t p2) : False.
Proof. exact (EQ_MP (@lem4380421 _105011 _105012 f s p1 t p2 h1 h2) (@lem4380011 _105012 t p2 h1)). Qed.
Lemma lem4380423 {_105011 _105012 : Type'} (f : type686 _105011) (s : _105011 -> Prop) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) (h1 : term246 _105011 s p1) (h2 : term263 _105011 _105012 f s p1 t p2) : (term246 _105011 s p1) = False.
Proof. exact (prop_ext (fun h3 : term246 _105011 s p1 => @lem4380418 _105011 _105012 f s p1 t p2 h1 h2) (fun h3 : False => @lem4379982 _105011 s p1 h1)). Qed.
Lemma lem4380424 {_105011 _105012 : Type'} (f : type686 _105011) (s : _105011 -> Prop) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) (h1 : term246 _105011 s p1) (h2 : term263 _105011 _105012 f s p1 t p2) : False.
Proof. exact (EQ_MP (@lem4380423 _105011 _105012 f s p1 t p2 h1 h2) (@lem4379982 _105011 s p1 h1)). Qed.
Lemma lem4380425 {_105011 _105012 : Type'} (x : _105011 -> Prop) (s : _105011 -> Prop) (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) (h1 : f x) (h2 : term252 _105011 _105012 s f p1 t p2) : False.
Proof. exact (or_elim (@lem4379949 _105011 _105012 s f p1 t p2 h2) (fun h0 : term248 _105011 f s p1 => @lem4380330 _105011 _105012 s f p1 t p2 h0 h2) (fun h0 : term246 _105012 t p2 => @lem4380420 _105011 _105012 x s f p1 t p2 h0 h1 h2)). Qed.
Lemma lem4380426 {_105011 _105012 : Type'} (f : type686 _105011) (s : _105011 -> Prop) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) (h1 : term263 _105011 _105012 f s p1 t p2) : False.
Proof. exact (or_elim (@lem4379942 _105011 _105012 f s p1 t p2 h1) (fun h0 : term246 _105011 s p1 => @lem4380424 _105011 _105012 f s p1 t p2 h0 h1) (fun h0 : term246 _105012 t p2 => @lem4380422 _105011 _105012 f s p1 t p2 h0 h1)). Qed.
Lemma lem4380427 {_105011 _105012 : Type'} (x : _105011 -> Prop) (s : _105011 -> Prop) (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) (h1 : f x) (h2 : term231 _105011 _105012 s f p1 t p2) : False.
Proof. exact (or_elim (@lem4379929 _105011 _105012 s f p1 t p2 h2) (fun h0 : term263 _105011 _105012 f s p1 t p2 => @lem4380426 _105011 _105012 f s p1 t p2 h0) (fun h0 : term252 _105011 _105012 s f p1 t p2 => @lem4380425 _105011 _105012 x s f p1 t p2 h1 h0)). Qed.
Lemma lem4380428 {_105011 _105012 : Type'} (s : _105011 -> Prop) (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) (h1 : term47 _105011 f) (h2 : term231 _105011 _105012 s f p1 t p2) : False.
Proof. exact (ex_elim (@lem4379420 _105011 f h1) (fun x : _105011 -> Prop => fun h0 : term105 _105011 f x => @lem4380427 _105011 _105012 x s f p1 t p2 h0 h2)). Qed.
Lemma lem4380429 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) (h1 : term47 _105011 f) (h2 : term97 _105011 _105012 f p1 t p2) : False.
Proof. exact (ex_elim (@lem4379779 _105011 _105012 f p1 t p2 h2) (fun s : _105011 -> Prop => fun h0 : term233 _105011 _105012 f p1 t p2 s => @lem4380428 _105011 _105012 s f p1 t p2 h1 h0)). Qed.
Lemma lem4380430 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) (h1 : term47 _105011 f) (h2 : term97 _105011 _105012 f p1 t p2) : (term97 _105011 _105012 f p1 t p2) = False.
Proof. exact (prop_ext (fun h3 : term97 _105011 _105012 f p1 t p2 => @lem4380429 _105011 _105012 f p1 t p2 h1 h2) (fun h3 : False => @lem4379398 _105011 _105012 f p1 t p2 h2)). Qed.
Lemma lem4380431 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) (h1 : term47 _105011 f) (h2 : term97 _105011 _105012 f p1 t p2) : False.
Proof. exact (EQ_MP (@lem4380430 _105011 _105012 f p1 t p2 h1 h2) (@lem4379398 _105011 _105012 f p1 t p2 h2)). Qed.
Lemma lem4380432 {_105011 _105012 : Type'} (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) (f : type686 _105011) (h1 : term47 _105011 f) : term96 _105011 _105012 f p1 t p2.
Proof. exact (fun h0 : term97 _105011 _105012 f p1 t p2 => @lem4380431 _105011 _105012 f p1 t p2 h1 h0). Qed.
Lemma lem4380433 {_105011 _105012 : Type'} (p1 : _105011) (t : _105012 -> Prop) (p2 : _105012) (f : type686 _105011) (h1 : term47 _105011 f) : (term59 _105011 _105012 f p1 t p2) = (term71 _105011 _105012 f p1 t p2).
Proof. exact (EQ_MP (@lem4379397 _105011 _105012 f p1 t p2) (@lem4380432 _105011 _105012 p1 t p2 f h1)). Qed.
Lemma lem4380438 {_105011 _105012 : Type'} (p1 : _105011) (t : _105012 -> Prop) (f : type686 _105011) (h1 : term47 _105011 f) : term75 _105011 _105012 f p1 t.
Proof. exact (fun p2 : _105012 => @lem4380433 _105011 _105012 p1 t p2 f h1). Qed.
Lemma lem4380443 {_105011 _105012 : Type'} (t : _105012 -> Prop) (f : type686 _105011) (h1 : term47 _105011 f) : term78 _105011 _105012 f t.
Proof. exact (fun p1 : _105011 => @lem4380438 _105011 _105012 p1 t f h1). Qed.
Lemma lem4380444 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) : term79 _105011 _105012 f t.
Proof. exact (fun h0 : term47 _105011 f => @lem4380443 _105011 _105012 t f h0). Qed.
Lemma lem4380449 {_105011 _105012 : Type'} (t : _105012 -> Prop) : term91 _105011 _105012 t.
Proof. exact (fun f : type686 _105011 => @lem4380444 _105011 _105012 f t). Qed.
Lemma lem4380454 {_105011 _105012 : Type'} : term95 _105011 _105012.
Proof. exact (fun t : _105012 -> Prop => @lem4380449 _105011 _105012 t). Qed.
Lemma lem4380455 {_105011 _105012 : Type'} : term94 _105011 _105012.
Proof. exact (EQ_MP (@lem4379392 _105011 _105012) (@lem4380454 _105011 _105012)). Qed.
Lemma lem4380456 {_105011 _105012 : Type'} (t : _105012 -> Prop) : term291 _105011 _105012 t.
Proof. exact (@lem4380455 _105011 _105012 t). Qed.
Lemma lem4380457 {_105011 _105012 : Type'} (t : _105012 -> Prop) : (term291 _105011 _105012 t) = (term90 _105011 _105012 t).
Proof. exact (eq_refl (term291 _105011 _105012 t)). Qed.
Lemma lem4380458 {_105011 _105012 : Type'} (t : _105012 -> Prop) : term90 _105011 _105012 t.
Proof. exact (EQ_MP (@lem4380457 _105011 _105012 t) (@lem4380456 _105011 _105012 t)). Qed.
Lemma lem4380459 {_105011 _105012 : Type'} (t : _105012 -> Prop) (f : type686 _105011) : term292 _105011 _105012 t f.
Proof. exact (@lem4380458 _105011 _105012 t f). Qed.
Lemma lem4380460 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) : (term292 _105011 _105012 t f) = (term81 _105011 _105012 f t).
Proof. exact (eq_refl (term292 _105011 _105012 t f)). Qed.
Lemma lem4380461 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) : term81 _105011 _105012 f t.
Proof. exact (EQ_MP (@lem4380460 _105011 _105012 f t) (@lem4380459 _105011 _105012 t f)). Qed.
Lemma lem4380463 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) : term81 _105011 _105012 f t.
Proof. exact (@lem4379223 _105011 _105012 f t (@lem4380461 _105011 _105012 f t)). Qed.
Lemma lem4380464 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) (h1 : term82 _105011 _105012 f t) : False.
Proof. exact (@lem4380463 _105011 _105012 f t (@lem4379207 _105011 _105012 f t h1)). Qed.
Lemma lem4380465 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) (h1 : term82 _105011 _105012 f t) : (term82 _105011 _105012 f t) = False.
Proof. exact (prop_ext (fun h2 : term82 _105011 _105012 f t => @lem4380464 _105011 _105012 f t h1) (fun h2 : False => @lem4379207 _105011 _105012 f t h1)). Qed.
Lemma lem4380466 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) (h1 : term82 _105011 _105012 f t) : False.
Proof. exact (EQ_MP (@lem4380465 _105011 _105012 f t h1) (@lem4379207 _105011 _105012 f t h1)). Qed.
Lemma lem4380467 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) : term81 _105011 _105012 f t.
Proof. exact (fun h0 : term82 _105011 _105012 f t => @lem4380466 _105011 _105012 f t h0). Qed.
Lemma lem4380468 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) : term79 _105011 _105012 f t.
Proof. exact (EQ_MP (@lem4379206 _105011 _105012 f t) (@lem4380467 _105011 _105012 f t)). Qed.
Lemma lem4380469 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) : term46 _105011 _105012 f t.
Proof. exact (EQ_MP (@lem4379202 _105011 _105012 f t) (@lem4380468 _105011 _105012 f t)). Qed.
Lemma lem4380470 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) : term45 _105011 _105012 f t.
Proof. exact (EQ_MP (@lem4379057 _105011 _105012 f t) (@lem4380469 _105011 _105012 f t)). Qed.
Lemma lem4380471 {_105011 _105012 : Type'} (t : _105012 -> Prop) (f : type686 _105011) (h1 : term40 _105011 f) : term44 _105011 _105012 f t.
Proof. exact (@lem4380470 _105011 _105012 f t (@lem4372410 _105011 f h1)). Qed.
Lemma lem4380481 {_105011 _105012 : Type'} (t : _105012 -> Prop) (f : type686 _105011) (h1 : term40 _105011 f) : (term293 _105011 _105012 f t) = (term294 _105011 _105012 f t).
Proof. exact (EQ_MP (@lem4374285 _105011 _105012 f t) (@lem4380471 _105011 _105012 t f h1)). Qed.
Lemma lem4380482 {_105011 _105012 : Type'} (t : _105012 -> Prop) (f : type686 _105011) (h1 : term40 _105011 f) : (term40 _105011 f) = ((term293 _105011 _105012 f t) = (term294 _105011 _105012 f t)).
Proof. exact (prop_ext (fun h2 : term40 _105011 f => @lem4380481 _105011 _105012 t f h1) (fun h2 : (term293 _105011 _105012 f t) = (term294 _105011 _105012 f t) => @lem4372410 _105011 f h1)). Qed.
Lemma lem4380483 {_105011 _105012 : Type'} (t : _105012 -> Prop) (f : type686 _105011) (h1 : term40 _105011 f) : (term293 _105011 _105012 f t) = (term294 _105011 _105012 f t).
Proof. exact (EQ_MP (@lem4380482 _105011 _105012 t f h1) (@lem4372410 _105011 f h1)). Qed.
Lemma lem4380484 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) : term295 _105011 _105012 f t.
Proof. exact (fun h0 : term40 _105011 f => @lem4380483 _105011 _105012 t f h0). Qed.
Lemma lem4380485 {_105011 _105012 : Type'} (t : _105012 -> Prop) (f : type686 _105011) (h1 : f = (@EMPTY (_105011 -> Prop))) : (term293 _105011 _105012 f t) = (@CROSS _105012 _105011 (@UNIV _105011) t).
Proof. exact (EQ_MP (@lem4374001 _105011 _105012 t f h1) (@lem4379000 _105011 _105012 t f h1)). Qed.
Lemma lem4380486 {_105011 _105012 : Type'} (t : _105012 -> Prop) (f : type686 _105011) (h1 : f = (@EMPTY (_105011 -> Prop))) : (f = (@EMPTY (_105011 -> Prop))) = ((term293 _105011 _105012 f t) = (@CROSS _105012 _105011 (@UNIV _105011) t)).
Proof. exact (prop_ext (fun h2 : f = (@EMPTY (_105011 -> Prop)) => @lem4380485 _105011 _105012 t f h1) (fun h2 : (term293 _105011 _105012 f t) = (@CROSS _105012 _105011 (@UNIV _105011) t) => @lem4372393 _105011 f h1)). Qed.
Lemma lem4380487 {_105011 _105012 : Type'} (t : _105012 -> Prop) (f : type686 _105011) (h1 : f = (@EMPTY (_105011 -> Prop))) : (term293 _105011 _105012 f t) = (@CROSS _105012 _105011 (@UNIV _105011) t).
Proof. exact (EQ_MP (@lem4380486 _105011 _105012 t f h1) (@lem4372393 _105011 f h1)). Qed.
Lemma lem4380488 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) : term296 _105011 _105012 f t.
Proof. exact (fun h0 : f = (@EMPTY (_105011 -> Prop)) => @lem4380487 _105011 _105012 t f h0). Qed.
Lemma lem4380489 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) : term297 _105011 _105012 f t.
Proof. exact (conj (@lem4380488 _105011 _105012 f t) (@lem4380484 _105011 _105012 f t)). Qed.
Lemma lem4380490 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) : (term293 _105011 _105012 f t) = (term298 _105011 _105012 f t).
Proof. exact (EQ_MP (@lem4372392 _105011 _105012 f t) (@lem4380489 _105011 _105012 f t)). Qed.
