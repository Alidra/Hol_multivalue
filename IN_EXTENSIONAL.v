Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import IN_EXTENSIONAL_term_abbrevs.
Require Import EXTENSIONAL_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm3184736_spec.
Require Import thm3184739_spec.
Lemma lem4382823 {_83095 : Type'} : term0 _83095.
Proof. exact (EQ_MP (@lem3184739 _83095) (@lem3184736 _83095)). Qed.
Lemma lem4382824 {_83095 : Type'} (p : _83095 -> Prop) : term1 _83095 p.
Proof. exact (@lem4382823 _83095 p). Qed.
Lemma lem4382825 {_83095 : Type'} (p : _83095 -> Prop) : (term1 _83095 p) = (term2 _83095 p).
Proof. exact (eq_refl (term1 _83095 p)). Qed.
Lemma lem4382826 {_83095 : Type'} (p : _83095 -> Prop) : term2 _83095 p.
Proof. exact (EQ_MP (@lem4382825 _83095 p) (@lem4382824 _83095 p)). Qed.
Lemma lem4382827 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term3 _83095 p x.
Proof. exact (@lem4382826 _83095 p x). Qed.
Lemma lem4382828 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term3 _83095 p x) = ((term4 _83095 x p) = (p x)).
Proof. exact (eq_refl (term3 _83095 p x)). Qed.
Lemma lem4382837 {A B : Type'} (s : A -> Prop) : term5 A B s.
Proof. exact (@lem4382798 A B s). Qed.
Lemma lem4382838 {A B : Type'} (s : A -> Prop) : (term5 A B s) = ((@EXTENSIONAL A B s) = (term6 A B s)).
Proof. exact (eq_refl (term5 A B s)). Qed.
Lemma lem4382851 {A B : Type'} (s : A -> Prop) : (@EXTENSIONAL A B s) = (term6 A B s).
Proof. exact (EQ_MP (@lem4382838 A B s) (@lem4382837 A B s)). Qed.
Lemma lem4382852 {A B : Type'} (s : A -> Prop) : (@EXTENSIONAL A B s) = (term6 A B s).
Proof. exact (@lem4382851 A B s). Qed.
Lemma lem4382865 {A B : Type'} (f : A -> B) : (@IN (A -> B) f) = (@IN (A -> B) f).
Proof. exact (eq_refl (@IN (A -> B) f)). Qed.
Lemma lem4382866 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term7 A B f s) = (term8 A B f s).
Proof. exact (MK_COMB (@lem4382865 A B f) (@lem4382852 A B s)). Qed.
Lemma lem4382868 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term4 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem4382828 _83095 p x) (@lem4382827 _83095 p x)). Qed.
Lemma lem4382869 {A B : Type'} (p : type572 A B) (x : A -> B) : (term9 A B x p) = (p x).
Proof. exact (@lem4382868 (A -> B) p x). Qed.
Lemma lem4382870 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term10 A B f s) = (term11 A B s f).
Proof. exact (@lem4382869 A B (term12 A B s) f). Qed.
Lemma lem4382871 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term11 A B s f) = (term13 A B s f).
Proof. exact (eq_refl (term11 A B s f)). Qed.
Lemma lem4382872 {A B : Type'} (GEN_PVAR_139 : A -> B) : (@SETSPEC (A -> B) GEN_PVAR_139) = (@SETSPEC (A -> B) GEN_PVAR_139).
Proof. exact (eq_refl (@SETSPEC (A -> B) GEN_PVAR_139)). Qed.
Lemma lem4382873 {A B : Type'} (GEN_PVAR_139 : A -> B) (s : A -> Prop) (f : A -> B) : (term14 A B GEN_PVAR_139 s f) = (term15 A B GEN_PVAR_139 s f).
Proof. exact (MK_COMB (@lem4382872 A B GEN_PVAR_139) (@lem4382871 A B s f)). Qed.
Lemma lem4382874 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem4382875 {A B : Type'} (GEN_PVAR_139 : A -> B) (s : A -> Prop) (f : A -> B) : (term16 A B GEN_PVAR_139 s f) = (term17 A B GEN_PVAR_139 s f).
Proof. exact (MK_COMB (@lem4382873 A B GEN_PVAR_139 s f) (@lem4382874 A B f)). Qed.
Lemma lem4382876 {A B : Type'} (GEN_PVAR_139 : A -> B) (s : A -> Prop) : (term18 A B GEN_PVAR_139 s) = (term19 A B GEN_PVAR_139 s).
Proof. exact (fun_ext (fun f : A -> B => @lem4382875 A B GEN_PVAR_139 s f)). Qed.
Lemma lem4382877 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem4382878 {A B : Type'} (GEN_PVAR_139 : A -> B) (s : A -> Prop) : (term20 A B GEN_PVAR_139 s) = (term21 A B GEN_PVAR_139 s).
Proof. exact (MK_COMB (@lem4382877 A B) (@lem4382876 A B GEN_PVAR_139 s)). Qed.
Lemma lem4382879 {A B : Type'} (s : A -> Prop) : (term22 A B s) = (term23 A B s).
Proof. exact (fun_ext (fun GEN_PVAR_139 : A -> B => @lem4382878 A B GEN_PVAR_139 s)). Qed.
Lemma lem4382880 {A B : Type'} : (@GSPEC (A -> B)) = (@GSPEC (A -> B)).
Proof. exact (eq_refl (@GSPEC (A -> B))). Qed.
Lemma lem4382881 {A B : Type'} (s : A -> Prop) : (term24 A B s) = (term6 A B s).
Proof. exact (MK_COMB (@lem4382880 A B) (@lem4382879 A B s)). Qed.
Lemma lem4382882 {A B : Type'} (f : A -> B) : (@IN (A -> B) f) = (@IN (A -> B) f).
Proof. exact (eq_refl (@IN (A -> B) f)). Qed.
Lemma lem4382883 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term10 A B f s) = (term8 A B f s).
Proof. exact (MK_COMB (@lem4382882 A B f) (@lem4382881 A B s)). Qed.
Lemma lem4382884 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4382885 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term25 A B f s) = (term26 A B f s).
Proof. exact (MK_COMB (@lem4382884) (@lem4382883 A B f s)). Qed.
Lemma lem4382886 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term11 A B s f) = (term13 A B s f).
Proof. exact (eq_refl (term11 A B s f)). Qed.
Lemma lem4382887 {A B : Type'} (s : A -> Prop) (f : A -> B) : ((term10 A B f s) = (term11 A B s f)) = ((term8 A B f s) = (term13 A B s f)).
Proof. exact (MK_COMB (@lem4382885 A B f s) (@lem4382886 A B s f)). Qed.
Lemma lem4382888 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term8 A B f s) = (term13 A B s f).
Proof. exact (EQ_MP (@lem4382887 A B s f) (@lem4382870 A B s f)). Qed.
Lemma lem4382897 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term7 A B f s) = (term13 A B s f).
Proof. exact (TRANS (@lem4382866 A B f s) (@lem4382888 A B s f)). Qed.
Lemma lem4382898 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4382899 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term27 A B f s) = (term28 A B s f).
Proof. exact (MK_COMB (@lem4382898) (@lem4382897 A B s f)). Qed.
Lemma lem4382908 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term13 A B s f) = (term13 A B s f).
Proof. exact (eq_refl (term13 A B s f)). Qed.
Lemma lem4382909 {A B : Type'} (s : A -> Prop) (f : A -> B) : ((term7 A B f s) = (term13 A B s f)) = ((term13 A B s f) = (term13 A B s f)).
Proof. exact (MK_COMB (@lem4382899 A B s f) (@lem4382908 A B s f)). Qed.
Lemma lem4382911 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4382912 (x : Prop) : (x = x) = True.
Proof. exact (@lem4382911 Prop x). Qed.
Lemma lem4382913 {A B : Type'} (s : A -> Prop) (f : A -> B) : ((term13 A B s f) = (term13 A B s f)) = True.
Proof. exact (@lem4382912 (term13 A B s f)). Qed.
Lemma lem4382914 {A B : Type'} (s : A -> Prop) (f : A -> B) : ((term7 A B f s) = (term13 A B s f)) = True.
Proof. exact (TRANS (@lem4382909 A B s f) (@lem4382913 A B s f)). Qed.
Lemma lem4382915 {A B : Type'} (s : A -> Prop) : (term29 A B s) = (term30 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem4382914 A B s f)). Qed.
Lemma lem4382916 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4382917 {A B : Type'} (s : A -> Prop) : (term31 A B s) = (term32 A B).
Proof. exact (MK_COMB (@lem4382916 A B) (@lem4382915 A B s)). Qed.
Lemma lem4382919 {A : Type'} (t : Prop) : (term33 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4382920 {A B : Type'} (t : Prop) : (term34 A B t) = t.
Proof. exact (@lem4382919 (A -> B) t). Qed.
Lemma lem4382921 {A B : Type'} : (term32 A B) = True.
Proof. exact (@lem4382920 A B True). Qed.
Lemma lem4382922 {A B : Type'} (s : A -> Prop) : (term31 A B s) = True.
Proof. exact (TRANS (@lem4382917 A B s) (@lem4382921 A B)). Qed.
Lemma lem4382923 {A B : Type'} : (term35 A B) = (term36 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4382922 A B s)). Qed.
Lemma lem4382924 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4382925 {A B : Type'} : (term37 A B) = (term38 A).
Proof. exact (MK_COMB (@lem4382924 A) (@lem4382923 A B)). Qed.
Lemma lem4382927 {A : Type'} (t : Prop) : (term33 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4382928 {A : Type'} (t : Prop) : (term39 A t) = t.
Proof. exact (@lem4382927 (A -> Prop) t). Qed.
Lemma lem4382929 {A : Type'} : (term38 A) = True.
Proof. exact (@lem4382928 A True). Qed.
Lemma lem4382930 {A B : Type'} : (term37 A B) = True.
Proof. exact (TRANS (@lem4382925 A B) (@lem4382929 A)). Qed.
Lemma lem4382931 {A B : Type'} : True = (term37 A B).
Proof. exact (SYM (@lem4382930 A B)). Qed.
Lemma lem4382932 {A B : Type'} : term37 A B.
Proof. exact (EQ_MP (@lem4382931 A B) (@lem0)). Qed.
