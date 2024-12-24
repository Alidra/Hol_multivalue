Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import RESTRICTION_COMPOSE_RIGHT_term_abbrevs.
Require Import FUN_EQ_THM_spec.
Require Import RESTRICTION_spec.
Require Import o_DEF_spec.
Require Import thm0_spec.
Require Import thm12653_spec.
Require Import thm14781_spec.
Require Import thm15222_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Lemma lem4392851 {A B : Type'} (s : A -> Prop) : term0 A B s.
Proof. exact (@lem4386626 A B s). Qed.
Lemma lem4392852 {A B : Type'} (s : A -> Prop) : (term0 A B s) = (term1 A B s).
Proof. exact (eq_refl (term0 A B s)). Qed.
Lemma lem4392853 {A B : Type'} (s : A -> Prop) : term1 A B s.
Proof. exact (EQ_MP (@lem4392852 A B s) (@lem4392851 A B s)). Qed.
Lemma lem4392854 {A B : Type'} (s : A -> Prop) (f : A -> B) : term2 A B s f.
Proof. exact (@lem4392853 A B s f). Qed.
Lemma lem4392855 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term2 A B s f) = (term3 A B s f).
Proof. exact (eq_refl (term2 A B s f)). Qed.
Lemma lem4392856 {A B : Type'} (s : A -> Prop) (f : A -> B) : term3 A B s f.
Proof. exact (EQ_MP (@lem4392855 A B s f) (@lem4392854 A B s f)). Qed.
Lemma lem4392857 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : term4 A B s f x.
Proof. exact (@lem4392856 A B s f x). Qed.
Lemma lem4392858 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term4 A B s f x) = ((@RESTRICTION A B s f x) = (term5 A B s f x)).
Proof. exact (eq_refl (term4 A B s f x)). Qed.
Lemma lem4392860 {A B C : Type'} (f : B -> C) : term6 A B C f.
Proof. exact (@lem15397 A B C f). Qed.
Lemma lem4392861 {A B C : Type'} (f : B -> C) : (term6 A B C f) = (term7 A B C f).
Proof. exact (eq_refl (term6 A B C f)). Qed.
Lemma lem4392862 {A B C : Type'} (f : B -> C) : term7 A B C f.
Proof. exact (EQ_MP (@lem4392861 A B C f) (@lem4392860 A B C f)). Qed.
Lemma lem4392863 {A B C : Type'} (f : B -> C) (g : A -> B) : term8 A B C f g.
Proof. exact (@lem4392862 A B C f g). Qed.
Lemma lem4392864 {A B C : Type'} (f : B -> C) (g : A -> B) : (term8 A B C f g) = ((@o A B C f g) = (term9 A B C f g)).
Proof. exact (eq_refl (term8 A B C f g)). Qed.
Lemma lem4392866 {A B : Type'} (f : A -> B) : term10 A B f.
Proof. exact (@lem9220 A B f). Qed.
Lemma lem4392867 {A B : Type'} (f : A -> B) : (term10 A B f) = (term11 A B f).
Proof. exact (eq_refl (term10 A B f)). Qed.
Lemma lem4392868 {A B : Type'} (f : A -> B) : term11 A B f.
Proof. exact (EQ_MP (@lem4392867 A B f) (@lem4392866 A B f)). Qed.
Lemma lem4392869 {A B : Type'} (f : A -> B) (g : A -> B) : term12 A B f g.
Proof. exact (@lem4392868 A B f g). Qed.
Lemma lem4392870 {A B : Type'} (f : A -> B) (g : A -> B) : (term12 A B f g) = ((f = g) = (term13 A B f g)).
Proof. exact (eq_refl (term12 A B f g)). Qed.
Lemma lem4392887 {A B : Type'} (f : A -> B) (g : A -> B) : (f = g) = (term13 A B f g).
Proof. exact (EQ_MP (@lem4392870 A B f g) (@lem4392869 A B f g)). Qed.
Lemma lem4392888 {A C : Type'} (f : A -> C) (g : A -> C) : (f = g) = (term13 A C f g).
Proof. exact (@lem4392887 A C f g). Qed.
Lemma lem4392889 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) : ((term14 A B C g s f) = (term15 A B C s g f)) = (term16 A B C s g f).
Proof. exact (@lem4392888 A C (term14 A B C g s f) (term15 A B C s g f)). Qed.
Lemma lem4392899 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (@RESTRICTION A B s f x) = (term5 A B s f x).
Proof. exact (EQ_MP (@lem4392858 A B s f x) (@lem4392857 A B s f x)). Qed.
Lemma lem4392900 {A C : Type'} (s : A -> Prop) (f : A -> C) (x : A) : (@RESTRICTION A C s f x) = (term5 A C s f x).
Proof. exact (@lem4392899 A C s f x). Qed.
Lemma lem4392901 {A B C : Type'} (g : B -> C) (s : A -> Prop) (f : A -> B) (x : A) : (term17 A B C g s f x) = (term18 A B C g s f x).
Proof. exact (@lem4392900 A C s (term19 A B C g s f) x). Qed.
Lemma lem4392903 {A B C : Type'} (f : B -> C) (g : A -> B) : (@o A B C f g) = (term9 A B C f g).
Proof. exact (EQ_MP (@lem4392864 A B C f g) (@lem4392863 A B C f g)). Qed.
Lemma lem4392904 {A B C : Type'} (f : B -> C) (g : A -> B) : (@o A B C f g) = (term9 A B C f g).
Proof. exact (@lem4392903 A B C f g). Qed.
Lemma lem4392905 {A B C : Type'} (g : B -> C) (s : A -> Prop) (f : A -> B) : (term19 A B C g s f) = (term20 A B C g s f).
Proof. exact (@lem4392904 A B C g (@RESTRICTION A B s f)). Qed.
Lemma lem4392907 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (@RESTRICTION A B s f x) = (term5 A B s f x).
Proof. exact (EQ_MP (@lem4392858 A B s f x) (@lem4392857 A B s f x)). Qed.
Lemma lem4392908 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (@RESTRICTION A B s f x) = (term5 A B s f x).
Proof. exact (@lem4392907 A B s f x). Qed.
Lemma lem4392909 {B C : Type'} (g : B -> C) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem4392910 {A B C : Type'} (g : B -> C) (s : A -> Prop) (f : A -> B) (x : A) : (term21 A B C g s f x) = (term22 A B C g s f x).
Proof. exact (MK_COMB (@lem4392909 B C g) (@lem4392908 A B s f x)). Qed.
Lemma lem4392911 {A B C : Type'} (g : B -> C) (s : A -> Prop) (f : A -> B) : (term20 A B C g s f) = (term23 A B C g s f).
Proof. exact (fun_ext (fun x : A => @lem4392910 A B C g s f x)). Qed.
Lemma lem4392912 {A B C : Type'} (g : B -> C) (s : A -> Prop) (f : A -> B) : (term19 A B C g s f) = (term23 A B C g s f).
Proof. exact (TRANS (@lem4392905 A B C g s f) (@lem4392911 A B C g s f)). Qed.
Lemma lem4392913 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4392914 {A B C : Type'} (g : B -> C) (s : A -> Prop) (f : A -> B) (x : A) : (term24 A B C g s f x) = (term25 A B C g s f x).
Proof. exact (MK_COMB (@lem4392912 A B C g s f) (@lem4392913 A x)). Qed.
Lemma lem4392916 {A B : Type'} (f : A -> B) (y : A) : (term26 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4392917 {A C : Type'} (f : A -> C) (y : A) : (term26 A C f y) = (f y).
Proof. exact (@lem4392916 A C f y). Qed.
Lemma lem4392918 {A B C : Type'} (g : B -> C) (s : A -> Prop) (f : A -> B) (x : A) : (term27 A B C g s f x) = (term25 A B C g s f x).
Proof. exact (@lem4392917 A C (term23 A B C g s f) x). Qed.
Lemma lem4392919 {A B C : Type'} (g : B -> C) (s : A -> Prop) (f : A -> B) (x : A) : (term25 A B C g s f x) = (term22 A B C g s f x).
Proof. exact (eq_refl (term25 A B C g s f x)). Qed.
Lemma lem4392920 {A B C : Type'} (g : B -> C) (s : A -> Prop) (f : A -> B) : (term28 A B C g s f) = (term23 A B C g s f).
Proof. exact (fun_ext (fun x : A => @lem4392919 A B C g s f x)). Qed.
Lemma lem4392921 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4392922 {A B C : Type'} (g : B -> C) (s : A -> Prop) (f : A -> B) (x : A) : (term27 A B C g s f x) = (term25 A B C g s f x).
Proof. exact (MK_COMB (@lem4392920 A B C g s f) (@lem4392921 A x)). Qed.
Lemma lem4392923 {C : Type'} : (@eq C) = (@eq C).
Proof. exact (eq_refl (@eq C)). Qed.
Lemma lem4392924 {A B C : Type'} (g : B -> C) (s : A -> Prop) (f : A -> B) (x : A) : (term29 A B C g s f x) = (term30 A B C g s f x).
Proof. exact (MK_COMB (@lem4392923 C) (@lem4392922 A B C g s f x)). Qed.
Lemma lem4392925 {A B C : Type'} (g : B -> C) (s : A -> Prop) (f : A -> B) (x : A) : (term25 A B C g s f x) = (term22 A B C g s f x).
Proof. exact (eq_refl (term25 A B C g s f x)). Qed.
Lemma lem4392926 {A B C : Type'} (g : B -> C) (s : A -> Prop) (f : A -> B) (x : A) : ((term27 A B C g s f x) = (term25 A B C g s f x)) = ((term25 A B C g s f x) = (term22 A B C g s f x)).
Proof. exact (MK_COMB (@lem4392924 A B C g s f x) (@lem4392925 A B C g s f x)). Qed.
Lemma lem4392927 {A B C : Type'} (g : B -> C) (s : A -> Prop) (f : A -> B) (x : A) : (term25 A B C g s f x) = (term22 A B C g s f x).
Proof. exact (EQ_MP (@lem4392926 A B C g s f x) (@lem4392918 A B C g s f x)). Qed.
Lemma lem4392928 {A B C : Type'} (g : B -> C) (s : A -> Prop) (f : A -> B) (x : A) : (term24 A B C g s f x) = (term22 A B C g s f x).
Proof. exact (TRANS (@lem4392914 A B C g s f x) (@lem4392927 A B C g s f x)). Qed.
Lemma lem4392929 {A C : Type'} (x : A) (s : A -> Prop) : (term31 A C x s) = (term31 A C x s).
Proof. exact (eq_refl (term31 A C x s)). Qed.
Lemma lem4392930 {A B C : Type'} (g : B -> C) (s : A -> Prop) (f : A -> B) (x : A) : (term32 A B C g s f x) = (term33 A B C g s f x).
Proof. exact (MK_COMB (@lem4392929 A C x s) (@lem4392928 A B C g s f x)). Qed.
Lemma lem4392931 {C : Type'} : (@ARB C) = (@ARB C).
Proof. exact (eq_refl (@ARB C)). Qed.
Lemma lem4392932 {A B C : Type'} (g : B -> C) (s : A -> Prop) (f : A -> B) (x : A) : (term18 A B C g s f x) = (term34 A B C g s f x).
Proof. exact (MK_COMB (@lem4392930 A B C g s f x) (@lem4392931 C)). Qed.
Lemma lem4392933 {A B C : Type'} (g : B -> C) (s : A -> Prop) (f : A -> B) (x : A) : (term17 A B C g s f x) = (term34 A B C g s f x).
Proof. exact (TRANS (@lem4392901 A B C g s f x) (@lem4392932 A B C g s f x)). Qed.
Lemma lem4392934 {C : Type'} : (@eq C) = (@eq C).
Proof. exact (eq_refl (@eq C)). Qed.
Lemma lem4392935 {A B C : Type'} (g : B -> C) (s : A -> Prop) (f : A -> B) (x : A) : (term35 A B C g s f x) = (term36 A B C g s f x).
Proof. exact (MK_COMB (@lem4392934 C) (@lem4392933 A B C g s f x)). Qed.
Lemma lem4392937 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (@RESTRICTION A B s f x) = (term5 A B s f x).
Proof. exact (EQ_MP (@lem4392858 A B s f x) (@lem4392857 A B s f x)). Qed.
Lemma lem4392938 {A C : Type'} (s : A -> Prop) (f : A -> C) (x : A) : (@RESTRICTION A C s f x) = (term5 A C s f x).
Proof. exact (@lem4392937 A C s f x). Qed.
Lemma lem4392939 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (x : A) : (term37 A B C s g f x) = (term38 A B C s g f x).
Proof. exact (@lem4392938 A C s (@o A B C g f) x). Qed.
Lemma lem4392941 {A B C : Type'} (f : B -> C) (g : A -> B) : (@o A B C f g) = (term9 A B C f g).
Proof. exact (EQ_MP (@lem4392864 A B C f g) (@lem4392863 A B C f g)). Qed.
Lemma lem4392942 {A B C : Type'} (f : B -> C) (g : A -> B) : (@o A B C f g) = (term9 A B C f g).
Proof. exact (@lem4392941 A B C f g). Qed.
Lemma lem4392943 {A B C : Type'} (g : B -> C) (f : A -> B) : (@o A B C g f) = (term9 A B C g f).
Proof. exact (@lem4392942 A B C g f). Qed.
Lemma lem4392944 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4392945 {A B C : Type'} (g : B -> C) (f : A -> B) (x : A) : (@o A B C g f x) = (term39 A B C g f x).
Proof. exact (MK_COMB (@lem4392943 A B C g f) (@lem4392944 A x)). Qed.
Lemma lem4392947 {A B : Type'} (f : A -> B) (y : A) : (term26 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4392948 {A C : Type'} (f : A -> C) (y : A) : (term26 A C f y) = (f y).
Proof. exact (@lem4392947 A C f y). Qed.
Lemma lem4392949 {A B C : Type'} (g : B -> C) (f : A -> B) (x : A) : (term40 A B C g f x) = (term39 A B C g f x).
Proof. exact (@lem4392948 A C (term9 A B C g f) x). Qed.
Lemma lem4392950 {A B C : Type'} (g : B -> C) (f : A -> B) (x : A) : (term39 A B C g f x) = (term41 A B C g f x).
Proof. exact (eq_refl (term39 A B C g f x)). Qed.
Lemma lem4392951 {A B C : Type'} (g : B -> C) (f : A -> B) : (term42 A B C g f) = (term9 A B C g f).
Proof. exact (fun_ext (fun x : A => @lem4392950 A B C g f x)). Qed.
Lemma lem4392952 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4392953 {A B C : Type'} (g : B -> C) (f : A -> B) (x : A) : (term40 A B C g f x) = (term39 A B C g f x).
Proof. exact (MK_COMB (@lem4392951 A B C g f) (@lem4392952 A x)). Qed.
Lemma lem4392954 {C : Type'} : (@eq C) = (@eq C).
Proof. exact (eq_refl (@eq C)). Qed.
Lemma lem4392955 {A B C : Type'} (g : B -> C) (f : A -> B) (x : A) : (term43 A B C g f x) = (term44 A B C g f x).
Proof. exact (MK_COMB (@lem4392954 C) (@lem4392953 A B C g f x)). Qed.
Lemma lem4392956 {A B C : Type'} (g : B -> C) (f : A -> B) (x : A) : (term39 A B C g f x) = (term41 A B C g f x).
Proof. exact (eq_refl (term39 A B C g f x)). Qed.
Lemma lem4392957 {A B C : Type'} (g : B -> C) (f : A -> B) (x : A) : ((term40 A B C g f x) = (term39 A B C g f x)) = ((term39 A B C g f x) = (term41 A B C g f x)).
Proof. exact (MK_COMB (@lem4392955 A B C g f x) (@lem4392956 A B C g f x)). Qed.
Lemma lem4392958 {A B C : Type'} (g : B -> C) (f : A -> B) (x : A) : (term39 A B C g f x) = (term41 A B C g f x).
Proof. exact (EQ_MP (@lem4392957 A B C g f x) (@lem4392949 A B C g f x)). Qed.
Lemma lem4392959 {A B C : Type'} (g : B -> C) (f : A -> B) (x : A) : (@o A B C g f x) = (term41 A B C g f x).
Proof. exact (TRANS (@lem4392945 A B C g f x) (@lem4392958 A B C g f x)). Qed.
Lemma lem4392960 {A C : Type'} (x : A) (s : A -> Prop) : (term31 A C x s) = (term31 A C x s).
Proof. exact (eq_refl (term31 A C x s)). Qed.
Lemma lem4392961 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (x : A) : (term45 A B C s g f x) = (term46 A B C s g f x).
Proof. exact (MK_COMB (@lem4392960 A C x s) (@lem4392959 A B C g f x)). Qed.
Lemma lem4392962 {C : Type'} : (@ARB C) = (@ARB C).
Proof. exact (eq_refl (@ARB C)). Qed.
Lemma lem4392963 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (x : A) : (term38 A B C s g f x) = (term47 A B C s g f x).
Proof. exact (MK_COMB (@lem4392961 A B C s g f x) (@lem4392962 C)). Qed.
Lemma lem4392964 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (x : A) : (term37 A B C s g f x) = (term47 A B C s g f x).
Proof. exact (TRANS (@lem4392939 A B C s g f x) (@lem4392963 A B C s g f x)). Qed.
Lemma lem4392965 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (x : A) : ((term17 A B C g s f x) = (term37 A B C s g f x)) = ((term34 A B C g s f x) = (term47 A B C s g f x)).
Proof. exact (MK_COMB (@lem4392935 A B C g s f x) (@lem4392964 A B C s g f x)). Qed.
Lemma lem4392970 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) : (term48 A B C s g f) = (term49 A B C s g f).
Proof. exact (fun_ext (fun x : A => @lem4392965 A B C s g f x)). Qed.
Lemma lem4392971 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4392972 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) : (term16 A B C s g f) = (term50 A B C s g f).
Proof. exact (MK_COMB (@lem4392971 A) (@lem4392970 A B C s g f)). Qed.
Lemma lem4392977 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) : ((term14 A B C g s f) = (term15 A B C s g f)) = (term50 A B C s g f).
Proof. exact (TRANS (@lem4392889 A B C s g f) (@lem4392972 A B C s g f)). Qed.
Lemma lem4392978 {A B C : Type'} (g : B -> C) (f : A -> B) : (term51 A B C g f) = (term52 A B C g f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4392977 A B C s g f)). Qed.
Lemma lem4392979 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4392980 {A B C : Type'} (g : B -> C) (f : A -> B) : (term53 A B C g f) = (term54 A B C g f).
Proof. exact (MK_COMB (@lem4392979 A) (@lem4392978 A B C g f)). Qed.
Lemma lem4392985 {A B C : Type'} (f : A -> B) : (term55 A B C f) = (term56 A B C f).
Proof. exact (fun_ext (fun g : B -> C => @lem4392980 A B C g f)). Qed.
Lemma lem4392986 {B C : Type'} : (@all (B -> C)) = (@all (B -> C)).
Proof. exact (eq_refl (@all (B -> C))). Qed.
Lemma lem4392987 {A B C : Type'} (f : A -> B) : (term57 A B C f) = (term58 A B C f).
Proof. exact (MK_COMB (@lem4392986 B C) (@lem4392985 A B C f)). Qed.
Lemma lem4392992 {A B C : Type'} : (term59 A B C) = (term60 A B C).
Proof. exact (fun_ext (fun f : A -> B => @lem4392987 A B C f)). Qed.
Lemma lem4392993 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4392994 {A B C : Type'} : (term61 A B C) = (term62 A B C).
Proof. exact (MK_COMB (@lem4392993 A B) (@lem4392992 A B C)). Qed.
Lemma lem4392999 {A B C : Type'} : (term62 A B C) = (term61 A B C).
Proof. exact (SYM (@lem4392994 A B C)). Qed.
Lemma lem4393019 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term63 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem4393020 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term64 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem4393019 _2963 g t e g' t' e'). Qed.
Lemma lem4393021 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term65 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem4393020 _2963 g t e g' t'). Qed.
Lemma lem4393022 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term66 _2963 g t e.
Proof. exact (fun g' : Prop => @lem4393021 _2963 g t e g'). Qed.
Lemma lem4393023 {C : Type'} (g : Prop) (t : C) (e : C) : term66 C g t e.
Proof. exact (@lem4393022 C g t e). Qed.
Lemma lem4393024 {A B C : Type'} (g : B -> C) (s : A -> Prop) (f : A -> B) (x : A) : term67 A B C g s f x.
Proof. exact (@lem4393023 C (@IN A x s) (term22 A B C g s f x) (@ARB C)). Qed.
Lemma lem4393025 {A B C : Type'} (g : B -> C) (s : A -> Prop) (f : A -> B) (x : A) (g' : Prop) : term68 A B C g s f x g'.
Proof. exact (@lem4393024 A B C g s f x g'). Qed.
Lemma lem4393026 {A B C : Type'} (g : B -> C) (s : A -> Prop) (f : A -> B) (x : A) (g' : Prop) : (term68 A B C g s f x g') = (term69 A B C g s f x g').
Proof. exact (eq_refl (term68 A B C g s f x g')). Qed.
Lemma lem4393027 {A B C : Type'} (g : B -> C) (s : A -> Prop) (f : A -> B) (x : A) (g' : Prop) : term69 A B C g s f x g'.
Proof. exact (EQ_MP (@lem4393026 A B C g s f x g') (@lem4393025 A B C g s f x g')). Qed.
Lemma lem4393028 {A B C : Type'} (g : B -> C) (s : A -> Prop) (f : A -> B) (x : A) (g' : Prop) (t' : C) : term70 A B C g s f x g' t'.
Proof. exact (@lem4393027 A B C g s f x g' t'). Qed.
Lemma lem4393029 {A B C : Type'} (g : B -> C) (s : A -> Prop) (f : A -> B) (x : A) (g' : Prop) (t' : C) : (term70 A B C g s f x g' t') = (term71 A B C g s f x g' t').
Proof. exact (eq_refl (term70 A B C g s f x g' t')). Qed.
Lemma lem4393030 {A B C : Type'} (g : B -> C) (s : A -> Prop) (f : A -> B) (x : A) (g' : Prop) (t' : C) : term71 A B C g s f x g' t'.
Proof. exact (EQ_MP (@lem4393029 A B C g s f x g' t') (@lem4393028 A B C g s f x g' t')). Qed.
Lemma lem4393031 {A B C : Type'} (g : B -> C) (s : A -> Prop) (f : A -> B) (x : A) (g' : Prop) (t' : C) (e' : C) : term72 A B C g s f x g' t' e'.
Proof. exact (@lem4393030 A B C g s f x g' t' e'). Qed.
Lemma lem4393032 {A B C : Type'} (g : B -> C) (s : A -> Prop) (f : A -> B) (x : A) (g' : Prop) (t' : C) (e' : C) : (term72 A B C g s f x g' t' e') = (term73 A B C g s f x g' t' e').
Proof. exact (eq_refl (term72 A B C g s f x g' t' e')). Qed.
Lemma lem4393033 {A B C : Type'} (g : B -> C) (s : A -> Prop) (f : A -> B) (x : A) (g' : Prop) (t' : C) (e' : C) : term73 A B C g s f x g' t' e'.
Proof. exact (EQ_MP (@lem4393032 A B C g s f x g' t' e') (@lem4393031 A B C g s f x g' t' e')). Qed.
Lemma lem4393034 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (@IN A x s).
Proof. exact (eq_refl (@IN A x s)). Qed.
Lemma lem4393035 {A B C : Type'} (g : B -> C) (f : A -> B) (x : A) (s : A -> Prop) (t' : C) (e' : C) : term74 A B C g f x s t' e'.
Proof. exact (@lem4393033 A B C g s f x (@IN A x s) t' e'). Qed.
Lemma lem4393036 {A B C : Type'} (g : B -> C) (f : A -> B) (x : A) (s : A -> Prop) (t' : C) (e' : C) : term75 A B C g f x s t' e'.
Proof. exact (@lem4393035 A B C g f x s t' e' (@lem4393034 A x s)). Qed.
Lemma lem4393037 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (h1). Qed.
Lemma lem4393038 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = ((@IN A x s) = True).
Proof. exact (@lem7 (@IN A x s)). Qed.
Lemma lem4393041 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term63 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem4393042 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term64 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem4393041 _2963 g t e g' t' e'). Qed.
Lemma lem4393043 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term65 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem4393042 _2963 g t e g' t'). Qed.
Lemma lem4393044 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term66 _2963 g t e.
Proof. exact (fun g' : Prop => @lem4393043 _2963 g t e g'). Qed.
Lemma lem4393045 {B : Type'} (g : Prop) (t : B) (e : B) : term66 B g t e.
Proof. exact (@lem4393044 B g t e). Qed.
Lemma lem4393046 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : term76 A B s f x.
Proof. exact (@lem4393045 B (@IN A x s) (f x) (@ARB B)). Qed.
Lemma lem4393047 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (g' : Prop) : term77 A B s f x g'.
Proof. exact (@lem4393046 A B s f x g'). Qed.
Lemma lem4393048 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (g' : Prop) : (term77 A B s f x g') = (term78 A B s f x g').
Proof. exact (eq_refl (term77 A B s f x g')). Qed.
Lemma lem4393049 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (g' : Prop) : term78 A B s f x g'.
Proof. exact (EQ_MP (@lem4393048 A B s f x g') (@lem4393047 A B s f x g')). Qed.
Lemma lem4393050 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (g' : Prop) (t' : B) : term79 A B s f x g' t'.
Proof. exact (@lem4393049 A B s f x g' t'). Qed.
Lemma lem4393051 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (g' : Prop) (t' : B) : (term79 A B s f x g' t') = (term80 A B s f x g' t').
Proof. exact (eq_refl (term79 A B s f x g' t')). Qed.
Lemma lem4393052 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (g' : Prop) (t' : B) : term80 A B s f x g' t'.
Proof. exact (EQ_MP (@lem4393051 A B s f x g' t') (@lem4393050 A B s f x g' t')). Qed.
Lemma lem4393053 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (g' : Prop) (t' : B) (e' : B) : term81 A B s f x g' t' e'.
Proof. exact (@lem4393052 A B s f x g' t' e'). Qed.
Lemma lem4393054 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (g' : Prop) (t' : B) (e' : B) : (term81 A B s f x g' t' e') = (term82 A B s f x g' t' e').
Proof. exact (eq_refl (term81 A B s f x g' t' e')). Qed.
Lemma lem4393055 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (g' : Prop) (t' : B) (e' : B) : term82 A B s f x g' t' e'.
Proof. exact (EQ_MP (@lem4393054 A B s f x g' t' e') (@lem4393053 A B s f x g' t' e')). Qed.
Lemma lem4393057 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : (@IN A x s) = True.
Proof. exact (EQ_MP (@lem4393038 A x s) (@lem4393037 A x s h1)). Qed.
Lemma lem4393058 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (t' : B) (e' : B) : term83 A B s f x t' e'.
Proof. exact (@lem4393055 A B s f x True t' e'). Qed.
Lemma lem4393059 {A B : Type'} (f : A -> B) (t' : B) (e' : B) (x : A) (s : A -> Prop) (h1 : @IN A x s) : term84 A B s f x t' e'.
Proof. exact (@lem4393058 A B s f x t' e' (@lem4393057 A x s h1)). Qed.
Lemma lem4393065 {A B : Type'} (f : A -> B) (x : A) : (f x) = (f x).
Proof. exact (eq_refl (f x)). Qed.
Lemma lem4393066 {A B : Type'} (f : A -> B) (x : A) : term85 A B f x.
Proof. exact (fun h0 : True => @lem4393065 A B f x). Qed.
Lemma lem4393067 {A B : Type'} (f : A -> B) (e' : B) (x : A) (s : A -> Prop) (h1 : @IN A x s) : term86 A B s f x e'.
Proof. exact (@lem4393059 A B f (f x) e' x s h1). Qed.
Lemma lem4393068 {A B : Type'} (f : A -> B) (e' : B) (x : A) (s : A -> Prop) (h1 : @IN A x s) : term87 A B s f x e'.
Proof. exact (@lem4393067 A B f e' x s h1 (@lem4393066 A B f x)). Qed.
Lemma lem4393072 {B : Type'} : (@ARB B) = (@ARB B).
Proof. exact (eq_refl (@ARB B)). Qed.
Lemma lem4393073 {B : Type'} : term88 B.
Proof. exact (fun h0 : ~ True => @lem4393072 B). Qed.
Lemma lem4393074 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : @IN A x s) : term89 A B s f x.
Proof. exact (@lem4393068 A B f (@ARB B) x s h1). Qed.
Lemma lem4393075 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : @IN A x s) : (term5 A B s f x) = (term90 A B f x).
Proof. exact (@lem4393074 A B f x s h1 (@lem4393073 B)). Qed.
Lemma lem4393077 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem4393078 {B : Type'} (t2 : B) (t1 : B) : (@COND B True t1 t2) = t1.
Proof. exact (@lem4393077 B t2 t1). Qed.
Lemma lem4393079 {A B : Type'} (f : A -> B) (x : A) : (term90 A B f x) = (f x).
Proof. exact (@lem4393078 B (@ARB B) (f x)). Qed.
Lemma lem4393080 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : @IN A x s) : (term5 A B s f x) = (f x).
Proof. exact (TRANS (@lem4393075 A B f x s h1) (@lem4393079 A B f x)). Qed.
Lemma lem4393081 {B C : Type'} (g : B -> C) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem4393082 {A B C : Type'} (g : B -> C) (f : A -> B) (x : A) (s : A -> Prop) (h1 : @IN A x s) : (term22 A B C g s f x) = (term41 A B C g f x).
Proof. exact (MK_COMB (@lem4393081 B C g) (@lem4393080 A B f x s h1)). Qed.
Lemma lem4393083 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (x : A) : term91 A B C s g f x.
Proof. exact (fun h0 : @IN A x s => @lem4393082 A B C g f x s h0). Qed.
Lemma lem4393084 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (x : A) (e' : C) : term92 A B C s g f x e'.
Proof. exact (@lem4393036 A B C g f x s (term41 A B C g f x) e'). Qed.
Lemma lem4393085 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (x : A) (e' : C) : term93 A B C s g f x e'.
Proof. exact (@lem4393084 A B C s g f x e' (@lem4393083 A B C s g f x)). Qed.
Lemma lem4393089 {C : Type'} : (@ARB C) = (@ARB C).
Proof. exact (eq_refl (@ARB C)). Qed.
Lemma lem4393090 {A C : Type'} (x : A) (s : A -> Prop) : term94 A C x s.
Proof. exact (fun h0 : term95 A x s => @lem4393089 C). Qed.
Lemma lem4393091 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (x : A) : term96 A B C s g f x.
Proof. exact (@lem4393085 A B C s g f x (@ARB C)). Qed.
Lemma lem4393092 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (x : A) : (term34 A B C g s f x) = (term47 A B C s g f x).
Proof. exact (@lem4393091 A B C s g f x (@lem4393090 A C x s)). Qed.
Lemma lem4393126 {C : Type'} : (@eq C) = (@eq C).
Proof. exact (eq_refl (@eq C)). Qed.
Lemma lem4393127 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (x : A) : (term36 A B C g s f x) = (term97 A B C s g f x).
Proof. exact (MK_COMB (@lem4393126 C) (@lem4393092 A B C s g f x)). Qed.
Lemma lem4393194 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (x : A) : (term47 A B C s g f x) = (term47 A B C s g f x).
Proof. exact (eq_refl (term47 A B C s g f x)). Qed.
Lemma lem4393195 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (x : A) : ((term34 A B C g s f x) = (term47 A B C s g f x)) = ((term47 A B C s g f x) = (term47 A B C s g f x)).
Proof. exact (MK_COMB (@lem4393127 A B C s g f x) (@lem4393194 A B C s g f x)). Qed.
Lemma lem4393197 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4393198 {C : Type'} (x : C) : (x = x) = True.
Proof. exact (@lem4393197 C x). Qed.
Lemma lem4393199 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (x : A) : ((term47 A B C s g f x) = (term47 A B C s g f x)) = True.
Proof. exact (@lem4393198 C (term47 A B C s g f x)). Qed.
Lemma lem4393200 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (x : A) : ((term34 A B C g s f x) = (term47 A B C s g f x)) = True.
Proof. exact (TRANS (@lem4393195 A B C s g f x) (@lem4393199 A B C s g f x)). Qed.
Lemma lem4393201 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) : (term49 A B C s g f) = (term98 A).
Proof. exact (fun_ext (fun x : A => @lem4393200 A B C s g f x)). Qed.
Lemma lem4393202 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4393203 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) : (term50 A B C s g f) = (term99 A).
Proof. exact (MK_COMB (@lem4393202 A) (@lem4393201 A B C s g f)). Qed.
Lemma lem4393205 {A : Type'} (t : Prop) : (term100 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4393206 {A : Type'} (t : Prop) : (term100 A t) = t.
Proof. exact (@lem4393205 A t). Qed.
Lemma lem4393207 {A : Type'} : (term99 A) = True.
Proof. exact (@lem4393206 A True). Qed.
Lemma lem4393208 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) : (term50 A B C s g f) = True.
Proof. exact (TRANS (@lem4393203 A B C s g f) (@lem4393207 A)). Qed.
Lemma lem4393209 {A B C : Type'} (g : B -> C) (f : A -> B) : (term52 A B C g f) = (term101 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4393208 A B C s g f)). Qed.
Lemma lem4393210 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4393211 {A B C : Type'} (g : B -> C) (f : A -> B) : (term54 A B C g f) = (term102 A).
Proof. exact (MK_COMB (@lem4393210 A) (@lem4393209 A B C g f)). Qed.
Lemma lem4393213 {A : Type'} (t : Prop) : (term100 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4393214 {A : Type'} (t : Prop) : (term103 A t) = t.
Proof. exact (@lem4393213 (A -> Prop) t). Qed.
Lemma lem4393215 {A : Type'} : (term102 A) = True.
Proof. exact (@lem4393214 A True). Qed.
Lemma lem4393216 {A B C : Type'} (g : B -> C) (f : A -> B) : (term54 A B C g f) = True.
Proof. exact (TRANS (@lem4393211 A B C g f) (@lem4393215 A)). Qed.
Lemma lem4393217 {A B C : Type'} (f : A -> B) : (term56 A B C f) = (term104 B C).
Proof. exact (fun_ext (fun g : B -> C => @lem4393216 A B C g f)). Qed.
Lemma lem4393218 {B C : Type'} : (@all (B -> C)) = (@all (B -> C)).
Proof. exact (eq_refl (@all (B -> C))). Qed.
Lemma lem4393219 {A B C : Type'} (f : A -> B) : (term58 A B C f) = (term105 B C).
Proof. exact (MK_COMB (@lem4393218 B C) (@lem4393217 A B C f)). Qed.
Lemma lem4393221 {A : Type'} (t : Prop) : (term100 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4393222 {B C : Type'} (t : Prop) : (term106 B C t) = t.
Proof. exact (@lem4393221 (B -> C) t). Qed.
Lemma lem4393223 {B C : Type'} : (term105 B C) = True.
Proof. exact (@lem4393222 B C True). Qed.
Lemma lem4393224 {A B C : Type'} (f : A -> B) : (term58 A B C f) = True.
Proof. exact (TRANS (@lem4393219 A B C f) (@lem4393223 B C)). Qed.
Lemma lem4393225 {A B C : Type'} : (term60 A B C) = (term104 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem4393224 A B C f)). Qed.
Lemma lem4393226 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4393227 {A B C : Type'} : (term62 A B C) = (term105 A B).
Proof. exact (MK_COMB (@lem4393226 A B) (@lem4393225 A B C)). Qed.
Lemma lem4393229 {A : Type'} (t : Prop) : (term100 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4393230 {A B : Type'} (t : Prop) : (term106 A B t) = t.
Proof. exact (@lem4393229 (A -> B) t). Qed.
Lemma lem4393231 {A B : Type'} : (term105 A B) = True.
Proof. exact (@lem4393230 A B True). Qed.
Lemma lem4393232 {A B C : Type'} : (term62 A B C) = True.
Proof. exact (TRANS (@lem4393227 A B C) (@lem4393231 A B)). Qed.
Lemma lem4393233 {A B C : Type'} : True = (term62 A B C).
Proof. exact (SYM (@lem4393232 A B C)). Qed.
Lemma lem4393234 {A B C : Type'} : term62 A B C.
Proof. exact (EQ_MP (@lem4393233 A B C) (@lem0)). Qed.
Lemma lem4393235 {A B C : Type'} : term61 A B C.
Proof. exact (EQ_MP (@lem4392999 A B C) (@lem4393234 A B C)). Qed.
