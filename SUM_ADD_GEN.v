Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_ADD_GEN_term_abbrevs.
Require Import ITERATE_OP_GEN_spec.
Require Import MONOIDAL_REAL_ADD_spec.
Require Import NEUTRAL_REAL_ADD_spec.
Require Import support_spec.
Require Import thm7064097_spec.
Require Import thm7064111_spec.
Lemma lem7068797 {A B : Type'} (h1 : term0 A B) : term0 A B.
Proof. exact (h1). Qed.
Lemma lem7068798 {A B : Type'} (op : type1400 B) (h1 : term0 A B) : term1 A B op.
Proof. exact (@lem7068797 A B h1 op). Qed.
Lemma lem7068799 {A B : Type'} (op : type1400 B) : (term1 A B op) = (term2 A B op).
Proof. exact (eq_refl (term1 A B op)). Qed.
Lemma lem7068800 {A B : Type'} (op : type1400 B) (h1 : term0 A B) : term2 A B op.
Proof. exact (EQ_MP (@lem7068799 A B op) (@lem7068798 A B op h1)). Qed.
Lemma lem7068801 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : @monoidal B op.
Proof. exact (h1). Qed.
Lemma lem7068802 {A B : Type'} (op : type1400 B) (h1 : term0 A B) (h2 : @monoidal B op) : term3 A B op.
Proof. exact (@lem7068800 A B op h1 (@lem7068801 B op h2)). Qed.
Lemma lem7068803 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : term4 A B op.
Proof. exact (fun h0 : term0 A B => @lem7068802 A B op h0 h1). Qed.
Lemma lem7068804 {A B : Type'} (h1 : term0 A B) : term0 A B.
Proof. exact (h1). Qed.
Lemma lem7068805 {A B : Type'} (op : type1400 B) (h1 : term0 A B) (h2 : @monoidal B op) : term3 A B op.
Proof. exact (@lem7068803 A B op h2 (@lem7068804 A B h1)). Qed.
Lemma lem7068806 {A B : Type'} (op : type1400 B) (h1 : term0 A B) : term2 A B op.
Proof. exact (fun h0 : @monoidal B op => @lem7068805 A B op h1 h0). Qed.
Lemma lem7068807 {A B : Type'} (h1 : term0 A B) : term0 A B.
Proof. exact (fun op : type1400 B => @lem7068806 A B op h1). Qed.
Lemma lem7068808 {A B : Type'} : term5 A B.
Proof. exact (fun h0 : term0 A B => @lem7068807 A B h0). Qed.
Lemma lem7068809 {A B : Type'} : term0 A B.
Proof. exact (@lem7068808 A B (@lem6184258 A B)). Qed.
Lemma lem7068810 {A B : Type'} (op : type1400 B) : term1 A B op.
Proof. exact (@lem7068809 A B op). Qed.
Lemma lem7068811 {A B : Type'} (op : type1400 B) : (term1 A B op) = (term2 A B op).
Proof. exact (eq_refl (term1 A B op)). Qed.
Lemma lem7068816 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : (@support A B op f s) = (term6 A B s f op)) : (@support A B op f s) = (term6 A B s f op).
Proof. exact (h1). Qed.
Lemma lem7068817 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : (@support A B op f s) = (term6 A B s f op)) : (term6 A B s f op) = (@support A B op f s).
Proof. exact (SYM (@lem7068816 A B s f op h1)). Qed.
Lemma lem7068818 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : (term6 A B s f op) = (@support A B op f s)) : (term6 A B s f op) = (@support A B op f s).
Proof. exact (h1). Qed.
Lemma lem7068819 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : (term6 A B s f op) = (@support A B op f s)) : (@support A B op f s) = (term6 A B s f op).
Proof. exact (SYM (@lem7068818 A B op f s h1)). Qed.
Lemma lem7068820 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : ((@support A B op f s) = (term6 A B s f op)) = ((term6 A B s f op) = (@support A B op f s)).
Proof. exact (prop_ext (fun h1 : (@support A B op f s) = (term6 A B s f op) => @lem7068817 A B s f op h1) (fun h1 : (term6 A B s f op) = (@support A B op f s) => @lem7068819 A B op f s h1)). Qed.
Lemma lem7068821 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term7 A B s f) = (term8 A B f s).
Proof. exact (fun_ext (fun op : type1400 B => @lem7068820 A B op f s)). Qed.
Lemma lem7068822 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem7068823 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term9 A B s f) = (term10 A B f s).
Proof. exact (MK_COMB (@lem7068822 B) (@lem7068821 A B f s)). Qed.
Lemma lem7068824 {A B : Type'} (s : A -> Prop) : (term11 A B s) = (term12 A B s).
Proof. exact (fun_ext (fun f : A -> B => @lem7068823 A B f s)). Qed.
Lemma lem7068825 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem7068826 {A B : Type'} (s : A -> Prop) : (term13 A B s) = (term14 A B s).
Proof. exact (MK_COMB (@lem7068825 A B) (@lem7068824 A B s)). Qed.
Lemma lem7068827 {A B : Type'} : (term15 A B) = (term16 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7068826 A B s)). Qed.
Lemma lem7068828 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7068829 {A B : Type'} : (term17 A B) = (term18 A B).
Proof. exact (MK_COMB (@lem7068828 A) (@lem7068827 A B)). Qed.
Lemma lem7068830 {A B : Type'} : term18 A B.
Proof. exact (EQ_MP (@lem7068829 A B) (@lem5716761 A B)). Qed.
Lemma lem7068831 (h1 : (@neutral real real_add) = term19) : (@neutral real real_add) = term19.
Proof. exact (h1). Qed.
Lemma lem7068832 (h1 : (@neutral real real_add) = term19) : term19 = (@neutral real real_add).
Proof. exact (SYM (@lem7068831 h1)). Qed.
Lemma lem7068833 (h1 : term19 = (@neutral real real_add)) : term19 = (@neutral real real_add).
Proof. exact (h1). Qed.
Lemma lem7068834 (h1 : term19 = (@neutral real real_add)) : (@neutral real real_add) = term19.
Proof. exact (SYM (@lem7068833 h1)). Qed.
Lemma lem7068835 : ((@neutral real real_add) = term19) = (term19 = (@neutral real real_add)).
Proof. exact (prop_ext (fun h1 : (@neutral real real_add) = term19 => @lem7068832 h1) (fun h1 : term19 = (@neutral real real_add) => @lem7068834 h1)). Qed.
Lemma lem7068837 {A B : Type'} (s : A -> Prop) : term20 A B s.
Proof. exact (@lem7068830 A B s). Qed.
Lemma lem7068838 {A B : Type'} (s : A -> Prop) : (term20 A B s) = (term14 A B s).
Proof. exact (eq_refl (term20 A B s)). Qed.
Lemma lem7068839 {A B : Type'} (s : A -> Prop) : term14 A B s.
Proof. exact (EQ_MP (@lem7068838 A B s) (@lem7068837 A B s)). Qed.
Lemma lem7068840 {A B : Type'} (s : A -> Prop) (f : A -> B) : term21 A B s f.
Proof. exact (@lem7068839 A B s f). Qed.
Lemma lem7068841 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term21 A B s f) = (term10 A B f s).
Proof. exact (eq_refl (term21 A B s f)). Qed.
Lemma lem7068842 {A B : Type'} (f : A -> B) (s : A -> Prop) : term10 A B f s.
Proof. exact (EQ_MP (@lem7068841 A B f s) (@lem7068840 A B s f)). Qed.
Lemma lem7068843 {A B : Type'} (f : A -> B) (s : A -> Prop) (op : type1400 B) : term22 A B f s op.
Proof. exact (@lem7068842 A B f s op). Qed.
Lemma lem7068844 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term22 A B f s op) = ((term6 A B s f op) = (@support A B op f s)).
Proof. exact (eq_refl (term22 A B f s op)). Qed.
Lemma lem7068871 : term19 = (@neutral real real_add).
Proof. exact (EQ_MP (@lem7068835) (@lem7065438)). Qed.
Lemma lem7068872 {_131804 : Type'} (f : _131804 -> real) (x : _131804) : (term23 _131804 f x) = (term23 _131804 f x).
Proof. exact (eq_refl (term23 _131804 f x)). Qed.
Lemma lem7068873 {_131804 : Type'} (f : _131804 -> real) (x : _131804) : ((f x) = term19) = ((f x) = (@neutral real real_add)).
Proof. exact (MK_COMB (@lem7068872 _131804 f x) (@lem7068871)). Qed.
Lemma lem7068876 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7068877 {_131804 : Type'} (f : _131804 -> real) (x : _131804) : (term24 _131804 f x) = (term25 _131804 f x).
Proof. exact (MK_COMB (@lem7068876) (@lem7068873 _131804 f x)). Qed.
Lemma lem7068878 {_131804 : Type'} (x : _131804) (s : _131804 -> Prop) : (term26 _131804 x s) = (term26 _131804 x s).
Proof. exact (eq_refl (term26 _131804 x s)). Qed.
Lemma lem7068879 {_131804 : Type'} (s : _131804 -> Prop) (f : _131804 -> real) (x : _131804) : (term27 _131804 s f x) = (term28 _131804 s f x).
Proof. exact (MK_COMB (@lem7068878 _131804 x s) (@lem7068877 _131804 f x)). Qed.
Lemma lem7068882 {_131804 : Type'} (GEN_PVAR_312 : _131804) : (@SETSPEC _131804 GEN_PVAR_312) = (@SETSPEC _131804 GEN_PVAR_312).
Proof. exact (eq_refl (@SETSPEC _131804 GEN_PVAR_312)). Qed.
Lemma lem7068883 {_131804 : Type'} (GEN_PVAR_312 : _131804) (s : _131804 -> Prop) (f : _131804 -> real) (x : _131804) : (term29 _131804 GEN_PVAR_312 s f x) = (term30 _131804 GEN_PVAR_312 s f x).
Proof. exact (MK_COMB (@lem7068882 _131804 GEN_PVAR_312) (@lem7068879 _131804 s f x)). Qed.
Lemma lem7068884 {_131804 : Type'} (x : _131804) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7068885 {_131804 : Type'} (GEN_PVAR_312 : _131804) (s : _131804 -> Prop) (f : _131804 -> real) (x : _131804) : (term31 _131804 GEN_PVAR_312 s f x) = (term32 _131804 GEN_PVAR_312 s f x).
Proof. exact (MK_COMB (@lem7068883 _131804 GEN_PVAR_312 s f x) (@lem7068884 _131804 x)). Qed.
Lemma lem7068886 {_131804 : Type'} (GEN_PVAR_312 : _131804) (s : _131804 -> Prop) (f : _131804 -> real) : (term33 _131804 GEN_PVAR_312 s f) = (term34 _131804 GEN_PVAR_312 s f).
Proof. exact (fun_ext (fun x : _131804 => @lem7068885 _131804 GEN_PVAR_312 s f x)). Qed.
Lemma lem7068887 {_131804 : Type'} : (@ex _131804) = (@ex _131804).
Proof. exact (eq_refl (@ex _131804)). Qed.
Lemma lem7068888 {_131804 : Type'} (GEN_PVAR_312 : _131804) (s : _131804 -> Prop) (f : _131804 -> real) : (term35 _131804 GEN_PVAR_312 s f) = (term36 _131804 GEN_PVAR_312 s f).
Proof. exact (MK_COMB (@lem7068887 _131804) (@lem7068886 _131804 GEN_PVAR_312 s f)). Qed.
Lemma lem7068893 {_131804 : Type'} (s : _131804 -> Prop) (f : _131804 -> real) : (term37 _131804 s f) = (term38 _131804 s f).
Proof. exact (fun_ext (fun GEN_PVAR_312 : _131804 => @lem7068888 _131804 GEN_PVAR_312 s f)). Qed.
Lemma lem7068894 {_131804 : Type'} : (@GSPEC _131804) = (@GSPEC _131804).
Proof. exact (eq_refl (@GSPEC _131804)). Qed.
Lemma lem7068895 {_131804 : Type'} (s : _131804 -> Prop) (f : _131804 -> real) : (term39 _131804 s f) = (term40 _131804 s f).
Proof. exact (MK_COMB (@lem7068894 _131804) (@lem7068893 _131804 s f)). Qed.
Lemma lem7068897 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term6 A B s f op) = (@support A B op f s).
Proof. exact (EQ_MP (@lem7068844 A B op f s) (@lem7068843 A B f s op)). Qed.
Lemma lem7068898 {_131804 : Type'} (op : type1627) (f : _131804 -> real) (s : _131804 -> Prop) : (term41 _131804 s f op) = (@support _131804 real op f s).
Proof. exact (@lem7068897 _131804 real op f s). Qed.
Lemma lem7068899 {_131804 : Type'} (f : _131804 -> real) (s : _131804 -> Prop) : (term40 _131804 s f) = (@support _131804 real real_add f s).
Proof. exact (@lem7068898 _131804 real_add f s). Qed.
Lemma lem7068900 {_131804 : Type'} (f : _131804 -> real) (s : _131804 -> Prop) : (term39 _131804 s f) = (@support _131804 real real_add f s).
Proof. exact (TRANS (@lem7068895 _131804 s f) (@lem7068899 _131804 f s)). Qed.
Lemma lem7068901 {_131804 : Type'} : (@FINITE _131804) = (@FINITE _131804).
Proof. exact (eq_refl (@FINITE _131804)). Qed.
Lemma lem7068902 {_131804 : Type'} (f : _131804 -> real) (s : _131804 -> Prop) : (term42 _131804 s f) = (term43 _131804 f s).
Proof. exact (MK_COMB (@lem7068901 _131804) (@lem7068900 _131804 f s)). Qed.
Lemma lem7068903 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7068904 {_131804 : Type'} (f : _131804 -> real) (s : _131804 -> Prop) : (term44 _131804 s f) = (term45 _131804 f s).
Proof. exact (MK_COMB (@lem7068903) (@lem7068902 _131804 f s)). Qed.
Lemma lem7068914 : term19 = (@neutral real real_add).
Proof. exact (EQ_MP (@lem7068835) (@lem7065438)). Qed.
Lemma lem7068915 {_131804 : Type'} (g : _131804 -> real) (x : _131804) : (term23 _131804 g x) = (term23 _131804 g x).
Proof. exact (eq_refl (term23 _131804 g x)). Qed.
Lemma lem7068916 {_131804 : Type'} (g : _131804 -> real) (x : _131804) : ((g x) = term19) = ((g x) = (@neutral real real_add)).
Proof. exact (MK_COMB (@lem7068915 _131804 g x) (@lem7068914)). Qed.
Lemma lem7068919 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7068920 {_131804 : Type'} (g : _131804 -> real) (x : _131804) : (term24 _131804 g x) = (term25 _131804 g x).
Proof. exact (MK_COMB (@lem7068919) (@lem7068916 _131804 g x)). Qed.
Lemma lem7068921 {_131804 : Type'} (x : _131804) (s : _131804 -> Prop) : (term26 _131804 x s) = (term26 _131804 x s).
Proof. exact (eq_refl (term26 _131804 x s)). Qed.
Lemma lem7068922 {_131804 : Type'} (s : _131804 -> Prop) (g : _131804 -> real) (x : _131804) : (term27 _131804 s g x) = (term28 _131804 s g x).
Proof. exact (MK_COMB (@lem7068921 _131804 x s) (@lem7068920 _131804 g x)). Qed.
Lemma lem7068925 {_131804 : Type'} (GEN_PVAR_313 : _131804) : (@SETSPEC _131804 GEN_PVAR_313) = (@SETSPEC _131804 GEN_PVAR_313).
Proof. exact (eq_refl (@SETSPEC _131804 GEN_PVAR_313)). Qed.
Lemma lem7068926 {_131804 : Type'} (GEN_PVAR_313 : _131804) (s : _131804 -> Prop) (g : _131804 -> real) (x : _131804) : (term29 _131804 GEN_PVAR_313 s g x) = (term30 _131804 GEN_PVAR_313 s g x).
Proof. exact (MK_COMB (@lem7068925 _131804 GEN_PVAR_313) (@lem7068922 _131804 s g x)). Qed.
Lemma lem7068927 {_131804 : Type'} (x : _131804) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7068928 {_131804 : Type'} (GEN_PVAR_313 : _131804) (s : _131804 -> Prop) (g : _131804 -> real) (x : _131804) : (term31 _131804 GEN_PVAR_313 s g x) = (term32 _131804 GEN_PVAR_313 s g x).
Proof. exact (MK_COMB (@lem7068926 _131804 GEN_PVAR_313 s g x) (@lem7068927 _131804 x)). Qed.
Lemma lem7068929 {_131804 : Type'} (GEN_PVAR_313 : _131804) (s : _131804 -> Prop) (g : _131804 -> real) : (term33 _131804 GEN_PVAR_313 s g) = (term34 _131804 GEN_PVAR_313 s g).
Proof. exact (fun_ext (fun x : _131804 => @lem7068928 _131804 GEN_PVAR_313 s g x)). Qed.
Lemma lem7068930 {_131804 : Type'} : (@ex _131804) = (@ex _131804).
Proof. exact (eq_refl (@ex _131804)). Qed.
Lemma lem7068931 {_131804 : Type'} (GEN_PVAR_313 : _131804) (s : _131804 -> Prop) (g : _131804 -> real) : (term35 _131804 GEN_PVAR_313 s g) = (term36 _131804 GEN_PVAR_313 s g).
Proof. exact (MK_COMB (@lem7068930 _131804) (@lem7068929 _131804 GEN_PVAR_313 s g)). Qed.
Lemma lem7068936 {_131804 : Type'} (s : _131804 -> Prop) (g : _131804 -> real) : (term37 _131804 s g) = (term38 _131804 s g).
Proof. exact (fun_ext (fun GEN_PVAR_313 : _131804 => @lem7068931 _131804 GEN_PVAR_313 s g)). Qed.
Lemma lem7068937 {_131804 : Type'} : (@GSPEC _131804) = (@GSPEC _131804).
Proof. exact (eq_refl (@GSPEC _131804)). Qed.
Lemma lem7068938 {_131804 : Type'} (s : _131804 -> Prop) (g : _131804 -> real) : (term39 _131804 s g) = (term40 _131804 s g).
Proof. exact (MK_COMB (@lem7068937 _131804) (@lem7068936 _131804 s g)). Qed.
Lemma lem7068940 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term6 A B s f op) = (@support A B op f s).
Proof. exact (EQ_MP (@lem7068844 A B op f s) (@lem7068843 A B f s op)). Qed.
Lemma lem7068941 {_131804 : Type'} (op : type1627) (f : _131804 -> real) (s : _131804 -> Prop) : (term41 _131804 s f op) = (@support _131804 real op f s).
Proof. exact (@lem7068940 _131804 real op f s). Qed.
Lemma lem7068942 {_131804 : Type'} (g : _131804 -> real) (s : _131804 -> Prop) : (term40 _131804 s g) = (@support _131804 real real_add g s).
Proof. exact (@lem7068941 _131804 real_add g s). Qed.
Lemma lem7068943 {_131804 : Type'} (g : _131804 -> real) (s : _131804 -> Prop) : (term39 _131804 s g) = (@support _131804 real real_add g s).
Proof. exact (TRANS (@lem7068938 _131804 s g) (@lem7068942 _131804 g s)). Qed.
Lemma lem7068944 {_131804 : Type'} : (@FINITE _131804) = (@FINITE _131804).
Proof. exact (eq_refl (@FINITE _131804)). Qed.
Lemma lem7068945 {_131804 : Type'} (g : _131804 -> real) (s : _131804 -> Prop) : (term42 _131804 s g) = (term43 _131804 g s).
Proof. exact (MK_COMB (@lem7068944 _131804) (@lem7068943 _131804 g s)). Qed.
Lemma lem7068946 {_131804 : Type'} (f : _131804 -> real) (g : _131804 -> real) (s : _131804 -> Prop) : (term46 _131804 f s g) = (term47 _131804 f g s).
Proof. exact (MK_COMB (@lem7068904 _131804 f s) (@lem7068945 _131804 g s)). Qed.
Lemma lem7068949 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7068950 {_131804 : Type'} (f : _131804 -> real) (g : _131804 -> real) (s : _131804 -> Prop) : (term48 _131804 f s g) = (term49 _131804 f g s).
Proof. exact (MK_COMB (@lem7068949) (@lem7068946 _131804 f g s)). Qed.
Lemma lem7068954 {_131408 : Type'} : (@sum _131408) = (@iterate real _131408 real_add).
Proof. exact (TRANS (@lem7064097 _131408) (@lem7064111 _131408)). Qed.
Lemma lem7068955 {_131804 : Type'} : (@sum _131804) = (@iterate real _131804 real_add).
Proof. exact (@lem7068954 _131804). Qed.
Lemma lem7068956 {_131804 : Type'} (s : _131804 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7068957 {_131804 : Type'} (s : _131804 -> Prop) : (@sum _131804 s) = (@iterate real _131804 real_add s).
Proof. exact (MK_COMB (@lem7068955 _131804) (@lem7068956 _131804 s)). Qed.
Lemma lem7068958 {_131804 : Type'} (f : _131804 -> real) (g : _131804 -> real) : (term50 _131804 f g) = (term50 _131804 f g).
Proof. exact (eq_refl (term50 _131804 f g)). Qed.
Lemma lem7068959 {_131804 : Type'} (s : _131804 -> Prop) (f : _131804 -> real) (g : _131804 -> real) : (term51 _131804 s f g) = (term52 _131804 s f g).
Proof. exact (MK_COMB (@lem7068957 _131804 s) (@lem7068958 _131804 f g)). Qed.
Lemma lem7068960 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7068961 {_131804 : Type'} (s : _131804 -> Prop) (f : _131804 -> real) (g : _131804 -> real) : (term53 _131804 s f g) = (term54 _131804 s f g).
Proof. exact (MK_COMB (@lem7068960) (@lem7068959 _131804 s f g)). Qed.
Lemma lem7068963 {_131408 : Type'} : (@sum _131408) = (@iterate real _131408 real_add).
Proof. exact (TRANS (@lem7064097 _131408) (@lem7064111 _131408)). Qed.
Lemma lem7068964 {_131804 : Type'} : (@sum _131804) = (@iterate real _131804 real_add).
Proof. exact (@lem7068963 _131804). Qed.
Lemma lem7068965 {_131804 : Type'} (s : _131804 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7068966 {_131804 : Type'} (s : _131804 -> Prop) : (@sum _131804 s) = (@iterate real _131804 real_add s).
Proof. exact (MK_COMB (@lem7068964 _131804) (@lem7068965 _131804 s)). Qed.
Lemma lem7068967 {_131804 : Type'} (f : _131804 -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7068968 {_131804 : Type'} (s : _131804 -> Prop) (f : _131804 -> real) : (@sum _131804 s f) = (@iterate real _131804 real_add s f).
Proof. exact (MK_COMB (@lem7068966 _131804 s) (@lem7068967 _131804 f)). Qed.
Lemma lem7068969 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7068970 {_131804 : Type'} (s : _131804 -> Prop) (f : _131804 -> real) : (term55 _131804 s f) = (term56 _131804 s f).
Proof. exact (MK_COMB (@lem7068969) (@lem7068968 _131804 s f)). Qed.
Lemma lem7068972 {_131408 : Type'} : (@sum _131408) = (@iterate real _131408 real_add).
Proof. exact (TRANS (@lem7064097 _131408) (@lem7064111 _131408)). Qed.
Lemma lem7068973 {_131804 : Type'} : (@sum _131804) = (@iterate real _131804 real_add).
Proof. exact (@lem7068972 _131804). Qed.
Lemma lem7068974 {_131804 : Type'} (s : _131804 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7068975 {_131804 : Type'} (s : _131804 -> Prop) : (@sum _131804 s) = (@iterate real _131804 real_add s).
Proof. exact (MK_COMB (@lem7068973 _131804) (@lem7068974 _131804 s)). Qed.
Lemma lem7068976 {_131804 : Type'} (g : _131804 -> real) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem7068977 {_131804 : Type'} (s : _131804 -> Prop) (g : _131804 -> real) : (@sum _131804 s g) = (@iterate real _131804 real_add s g).
Proof. exact (MK_COMB (@lem7068975 _131804 s) (@lem7068976 _131804 g)). Qed.
Lemma lem7068978 {_131804 : Type'} (f : _131804 -> real) (s : _131804 -> Prop) (g : _131804 -> real) : (term57 _131804 f s g) = (term58 _131804 f s g).
Proof. exact (MK_COMB (@lem7068970 _131804 s f) (@lem7068977 _131804 s g)). Qed.
Lemma lem7068979 {_131804 : Type'} (f : _131804 -> real) (s : _131804 -> Prop) (g : _131804 -> real) : ((term51 _131804 s f g) = (term57 _131804 f s g)) = ((term52 _131804 s f g) = (term58 _131804 f s g)).
Proof. exact (MK_COMB (@lem7068961 _131804 s f g) (@lem7068978 _131804 f s g)). Qed.
Lemma lem7068982 {_131804 : Type'} (f : _131804 -> real) (s : _131804 -> Prop) (g : _131804 -> real) : (term59 _131804 f s g) = (term60 _131804 f s g).
Proof. exact (MK_COMB (@lem7068950 _131804 f g s) (@lem7068979 _131804 f s g)). Qed.
Lemma lem7068985 {_131804 : Type'} (f : _131804 -> real) (g : _131804 -> real) : (term61 _131804 f g) = (term62 _131804 f g).
Proof. exact (fun_ext (fun s : _131804 -> Prop => @lem7068982 _131804 f s g)). Qed.
Lemma lem7068986 {_131804 : Type'} : (@all (_131804 -> Prop)) = (@all (_131804 -> Prop)).
Proof. exact (eq_refl (@all (_131804 -> Prop))). Qed.
Lemma lem7068987 {_131804 : Type'} (f : _131804 -> real) (g : _131804 -> real) : (term63 _131804 f g) = (term64 _131804 f g).
Proof. exact (MK_COMB (@lem7068986 _131804) (@lem7068985 _131804 f g)). Qed.
Lemma lem7068992 {_131804 : Type'} (f : _131804 -> real) : (term65 _131804 f) = (term66 _131804 f).
Proof. exact (fun_ext (fun g : _131804 -> real => @lem7068987 _131804 f g)). Qed.
Lemma lem7068993 {_131804 : Type'} : (@all (_131804 -> real)) = (@all (_131804 -> real)).
Proof. exact (eq_refl (@all (_131804 -> real))). Qed.
Lemma lem7068994 {_131804 : Type'} (f : _131804 -> real) : (term67 _131804 f) = (term68 _131804 f).
Proof. exact (MK_COMB (@lem7068993 _131804) (@lem7068992 _131804 f)). Qed.
Lemma lem7068999 {_131804 : Type'} : (term69 _131804) = (term70 _131804).
Proof. exact (fun_ext (fun f : _131804 -> real => @lem7068994 _131804 f)). Qed.
Lemma lem7069000 {_131804 : Type'} : (@all (_131804 -> real)) = (@all (_131804 -> real)).
Proof. exact (eq_refl (@all (_131804 -> real))). Qed.
Lemma lem7069001 {_131804 : Type'} : (term71 _131804) = (term72 _131804).
Proof. exact (MK_COMB (@lem7069000 _131804) (@lem7068999 _131804)). Qed.
Lemma lem7069006 {_131804 : Type'} : (term72 _131804) = (term71 _131804).
Proof. exact (SYM (@lem7069001 _131804)). Qed.
Lemma lem7069008 {A B : Type'} (op : type1400 B) : term2 A B op.
Proof. exact (EQ_MP (@lem7068811 A B op) (@lem7068810 A B op)). Qed.
Lemma lem7069009 {_131804 : Type'} (op : type1627) : term73 _131804 op.
Proof. exact (@lem7069008 _131804 real op). Qed.
Lemma lem7069010 {_131804 : Type'} : term74 _131804.
Proof. exact (@lem7069009 _131804 real_add). Qed.
Lemma lem7069011 {_131804 : Type'} : term72 _131804.
Proof. exact (@lem7069010 _131804 (@lem7067132)). Qed.
Lemma lem7069012 {_131804 : Type'} : term71 _131804.
Proof. exact (EQ_MP (@lem7069006 _131804) (@lem7069011 _131804)). Qed.
