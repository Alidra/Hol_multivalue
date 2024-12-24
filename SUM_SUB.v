Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_SUB_term_abbrevs.
Require Import SUM_ADD_spec.
Require Import SUM_NEG_spec.
Require Import real_sub_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Lemma lem7070828 {_131713 : Type'} (f : _131713 -> real) : term0 _131713 f.
Proof. exact (@lem7068796 _131713 f). Qed.
Lemma lem7070829 {_131713 : Type'} (f : _131713 -> real) : (term0 _131713 f) = (term1 _131713 f).
Proof. exact (eq_refl (term0 _131713 f)). Qed.
Lemma lem7070830 {_131713 : Type'} (f : _131713 -> real) : term1 _131713 f.
Proof. exact (EQ_MP (@lem7070829 _131713 f) (@lem7070828 _131713 f)). Qed.
Lemma lem7070831 {_131713 : Type'} (f : _131713 -> real) (g : _131713 -> real) : term2 _131713 f g.
Proof. exact (@lem7070830 _131713 f g). Qed.
Lemma lem7070832 {_131713 : Type'} (f : _131713 -> real) (g : _131713 -> real) : (term2 _131713 f g) = (term3 _131713 f g).
Proof. exact (eq_refl (term2 _131713 f g)). Qed.
Lemma lem7070833 {_131713 : Type'} (f : _131713 -> real) (g : _131713 -> real) : term3 _131713 f g.
Proof. exact (EQ_MP (@lem7070832 _131713 f g) (@lem7070831 _131713 f g)). Qed.
Lemma lem7070834 {_131713 : Type'} (f : _131713 -> real) (g : _131713 -> real) (s : _131713 -> Prop) : term4 _131713 f g s.
Proof. exact (@lem7070833 _131713 f g s). Qed.
Lemma lem7070835 {_131713 : Type'} (f : _131713 -> real) (s : _131713 -> Prop) (g : _131713 -> real) : (term4 _131713 f g s) = (term5 _131713 f s g).
Proof. exact (eq_refl (term4 _131713 f g s)). Qed.
Lemma lem7070836 {_131713 : Type'} (f : _131713 -> real) (s : _131713 -> Prop) (g : _131713 -> real) : term5 _131713 f s g.
Proof. exact (EQ_MP (@lem7070835 _131713 f s g) (@lem7070834 _131713 f g s)). Qed.
Lemma lem7070837 {_131713 : Type'} (s : _131713 -> Prop) (h1 : @FINITE _131713 s) : @FINITE _131713 s.
Proof. exact (h1). Qed.
Lemma lem7070838 {_131713 : Type'} (f : _131713 -> real) (g : _131713 -> real) (s : _131713 -> Prop) (h1 : @FINITE _131713 s) : (term6 _131713 s f g) = (term7 _131713 f s g).
Proof. exact (@lem7070836 _131713 f s g (@lem7070837 _131713 s h1)). Qed.
Lemma lem7070844 {_132004 : Type'} (f : _132004 -> real) : term8 _132004 f.
Proof. exact (@lem7070827 _132004 f). Qed.
Lemma lem7070845 {_132004 : Type'} (f : _132004 -> real) : (term8 _132004 f) = (term9 _132004 f).
Proof. exact (eq_refl (term8 _132004 f)). Qed.
Lemma lem7070846 {_132004 : Type'} (f : _132004 -> real) : term9 _132004 f.
Proof. exact (EQ_MP (@lem7070845 _132004 f) (@lem7070844 _132004 f)). Qed.
Lemma lem7070847 {_132004 : Type'} (f : _132004 -> real) (s : _132004 -> Prop) : term10 _132004 f s.
Proof. exact (@lem7070846 _132004 f s). Qed.
Lemma lem7070848 {_132004 : Type'} (s : _132004 -> Prop) (f : _132004 -> real) : (term10 _132004 f s) = ((term11 _132004 s f) = (term12 _132004 s f)).
Proof. exact (eq_refl (term10 _132004 f s)). Qed.
Lemma lem7070850 (x : real) : term13 x.
Proof. exact (@lem1340977 x). Qed.
Lemma lem7070851 (x : real) : (term13 x) = (term14 x).
Proof. exact (eq_refl (term13 x)). Qed.
Lemma lem7070852 (x : real) : term14 x.
Proof. exact (EQ_MP (@lem7070851 x) (@lem7070850 x)). Qed.
Lemma lem7070853 (x : real) (y : real) : term15 x y.
Proof. exact (@lem7070852 x y). Qed.
Lemma lem7070854 (x : real) (y : real) : (term15 x y) = ((real_sub x y) = (term16 x y)).
Proof. exact (eq_refl (term15 x y)). Qed.
Lemma lem7070873 (x : real) (y : real) : (real_sub x y) = (term16 x y).
Proof. exact (EQ_MP (@lem7070854 x y) (@lem7070853 x y)). Qed.
Lemma lem7070874 {_132039 : Type'} (f : _132039 -> real) (g : _132039 -> real) (x : _132039) : (term17 _132039 f g x) = (term18 _132039 f g x).
Proof. exact (@lem7070873 (f x) (g x)). Qed.
Lemma lem7070875 {_132039 : Type'} (f : _132039 -> real) (g : _132039 -> real) : (term19 _132039 f g) = (term20 _132039 f g).
Proof. exact (fun_ext (fun x : _132039 => @lem7070874 _132039 f g x)). Qed.
Lemma lem7070876 {_132039 : Type'} (s : _132039 -> Prop) : (@sum _132039 s) = (@sum _132039 s).
Proof. exact (eq_refl (@sum _132039 s)). Qed.
Lemma lem7070877 {_132039 : Type'} (s : _132039 -> Prop) (f : _132039 -> real) (g : _132039 -> real) : (term21 _132039 s f g) = (term22 _132039 s f g).
Proof. exact (MK_COMB (@lem7070876 _132039 s) (@lem7070875 _132039 f g)). Qed.
Lemma lem7070878 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7070879 {_132039 : Type'} (s : _132039 -> Prop) (f : _132039 -> real) (g : _132039 -> real) : (term23 _132039 s f g) = (term24 _132039 s f g).
Proof. exact (MK_COMB (@lem7070878) (@lem7070877 _132039 s f g)). Qed.
Lemma lem7070881 (x : real) (y : real) : (real_sub x y) = (term16 x y).
Proof. exact (EQ_MP (@lem7070854 x y) (@lem7070853 x y)). Qed.
Lemma lem7070882 {_132039 : Type'} (f : _132039 -> real) (s : _132039 -> Prop) (g : _132039 -> real) : (term25 _132039 f s g) = (term26 _132039 f s g).
Proof. exact (@lem7070881 (@sum _132039 s f) (@sum _132039 s g)). Qed.
Lemma lem7070883 {_132039 : Type'} (f : _132039 -> real) (s : _132039 -> Prop) (g : _132039 -> real) : ((term21 _132039 s f g) = (term25 _132039 f s g)) = ((term22 _132039 s f g) = (term26 _132039 f s g)).
Proof. exact (MK_COMB (@lem7070879 _132039 s f g) (@lem7070882 _132039 f s g)). Qed.
Lemma lem7070884 {_132039 : Type'} (s : _132039 -> Prop) : (term27 _132039 s) = (term27 _132039 s).
Proof. exact (eq_refl (term27 _132039 s)). Qed.
Lemma lem7070885 {_132039 : Type'} (f : _132039 -> real) (s : _132039 -> Prop) (g : _132039 -> real) : (term28 _132039 f s g) = (term29 _132039 f s g).
Proof. exact (MK_COMB (@lem7070884 _132039 s) (@lem7070883 _132039 f s g)). Qed.
Lemma lem7070886 {_132039 : Type'} (f : _132039 -> real) (g : _132039 -> real) : (term30 _132039 f g) = (term31 _132039 f g).
Proof. exact (fun_ext (fun s : _132039 -> Prop => @lem7070885 _132039 f s g)). Qed.
Lemma lem7070887 {_132039 : Type'} : (@all (_132039 -> Prop)) = (@all (_132039 -> Prop)).
Proof. exact (eq_refl (@all (_132039 -> Prop))). Qed.
Lemma lem7070888 {_132039 : Type'} (f : _132039 -> real) (g : _132039 -> real) : (term32 _132039 f g) = (term33 _132039 f g).
Proof. exact (MK_COMB (@lem7070887 _132039) (@lem7070886 _132039 f g)). Qed.
Lemma lem7070889 {_132039 : Type'} (f : _132039 -> real) : (term34 _132039 f) = (term35 _132039 f).
Proof. exact (fun_ext (fun g : _132039 -> real => @lem7070888 _132039 f g)). Qed.
Lemma lem7070890 {_132039 : Type'} : (@all (_132039 -> real)) = (@all (_132039 -> real)).
Proof. exact (eq_refl (@all (_132039 -> real))). Qed.
Lemma lem7070891 {_132039 : Type'} (f : _132039 -> real) : (term36 _132039 f) = (term37 _132039 f).
Proof. exact (MK_COMB (@lem7070890 _132039) (@lem7070889 _132039 f)). Qed.
Lemma lem7070892 {_132039 : Type'} : (term38 _132039) = (term39 _132039).
Proof. exact (fun_ext (fun f : _132039 -> real => @lem7070891 _132039 f)). Qed.
Lemma lem7070893 {_132039 : Type'} : (@all (_132039 -> real)) = (@all (_132039 -> real)).
Proof. exact (eq_refl (@all (_132039 -> real))). Qed.
Lemma lem7070894 {_132039 : Type'} : (term40 _132039) = (term41 _132039).
Proof. exact (MK_COMB (@lem7070893 _132039) (@lem7070892 _132039)). Qed.
Lemma lem7070895 {_132039 : Type'} : (term41 _132039) = (term40 _132039).
Proof. exact (SYM (@lem7070894 _132039)). Qed.
Lemma lem7070911 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term42 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7070912 (p : Prop) (q : Prop) (p' : Prop) : term43 p q p'.
Proof. exact (fun q' : Prop => @lem7070911 p q p' q'). Qed.
Lemma lem7070913 (p : Prop) (q : Prop) : term44 p q.
Proof. exact (fun p' : Prop => @lem7070912 p q p'). Qed.
Lemma lem7070914 {_132039 : Type'} (f : _132039 -> real) (s : _132039 -> Prop) (g : _132039 -> real) : term45 _132039 f s g.
Proof. exact (@lem7070913 (@FINITE _132039 s) ((term22 _132039 s f g) = (term26 _132039 f s g))). Qed.
Lemma lem7070915 {_132039 : Type'} (f : _132039 -> real) (s : _132039 -> Prop) (g : _132039 -> real) (p' : Prop) : term46 _132039 f s g p'.
Proof. exact (@lem7070914 _132039 f s g p'). Qed.
Lemma lem7070916 {_132039 : Type'} (f : _132039 -> real) (s : _132039 -> Prop) (g : _132039 -> real) (p' : Prop) : (term46 _132039 f s g p') = (term47 _132039 f s g p').
Proof. exact (eq_refl (term46 _132039 f s g p')). Qed.
Lemma lem7070917 {_132039 : Type'} (f : _132039 -> real) (s : _132039 -> Prop) (g : _132039 -> real) (p' : Prop) : term47 _132039 f s g p'.
Proof. exact (EQ_MP (@lem7070916 _132039 f s g p') (@lem7070915 _132039 f s g p')). Qed.
Lemma lem7070918 {_132039 : Type'} (f : _132039 -> real) (s : _132039 -> Prop) (g : _132039 -> real) (p' : Prop) (q' : Prop) : term48 _132039 f s g p' q'.
Proof. exact (@lem7070917 _132039 f s g p' q'). Qed.
Lemma lem7070919 {_132039 : Type'} (f : _132039 -> real) (s : _132039 -> Prop) (g : _132039 -> real) (p' : Prop) (q' : Prop) : (term48 _132039 f s g p' q') = (term49 _132039 f s g p' q').
Proof. exact (eq_refl (term48 _132039 f s g p' q')). Qed.
Lemma lem7070920 {_132039 : Type'} (f : _132039 -> real) (s : _132039 -> Prop) (g : _132039 -> real) (p' : Prop) (q' : Prop) : term49 _132039 f s g p' q'.
Proof. exact (EQ_MP (@lem7070919 _132039 f s g p' q') (@lem7070918 _132039 f s g p' q')). Qed.
Lemma lem7070921 {_132039 : Type'} (s : _132039 -> Prop) : (@FINITE _132039 s) = (@FINITE _132039 s).
Proof. exact (eq_refl (@FINITE _132039 s)). Qed.
Lemma lem7070922 {_132039 : Type'} (f : _132039 -> real) (g : _132039 -> real) (s : _132039 -> Prop) (q' : Prop) : term50 _132039 f g s q'.
Proof. exact (@lem7070920 _132039 f s g (@FINITE _132039 s) q'). Qed.
Lemma lem7070923 {_132039 : Type'} (f : _132039 -> real) (g : _132039 -> real) (s : _132039 -> Prop) (q' : Prop) : term51 _132039 f g s q'.
Proof. exact (@lem7070922 _132039 f g s q' (@lem7070921 _132039 s)). Qed.
Lemma lem7070924 {_132039 : Type'} (s : _132039 -> Prop) (h1 : @FINITE _132039 s) : @FINITE _132039 s.
Proof. exact (h1). Qed.
Lemma lem7070925 {_132039 : Type'} (s : _132039 -> Prop) : (@FINITE _132039 s) = ((@FINITE _132039 s) = True).
Proof. exact (@lem7 (@FINITE _132039 s)). Qed.
Lemma lem7070930 {_131713 : Type'} (f : _131713 -> real) (s : _131713 -> Prop) (g : _131713 -> real) : term5 _131713 f s g.
Proof. exact (fun h0 : @FINITE _131713 s => @lem7070838 _131713 f g s h0). Qed.
Lemma lem7070931 {_132039 : Type'} (f : _132039 -> real) (s : _132039 -> Prop) (g : _132039 -> real) : term5 _132039 f s g.
Proof. exact (@lem7070930 _132039 f s g). Qed.
Lemma lem7070932 {_132039 : Type'} (f : _132039 -> real) (s : _132039 -> Prop) (g : _132039 -> real) : term52 _132039 f s g.
Proof. exact (@lem7070931 _132039 f s (term53 _132039 g)). Qed.
Lemma lem7070933 {_132039 : Type'} (g : _132039 -> real) (x : _132039) : (term54 _132039 g x) = (term55 _132039 g x).
Proof. exact (eq_refl (term54 _132039 g x)). Qed.
Lemma lem7070934 {_132039 : Type'} (f : _132039 -> real) (x : _132039) : (term56 _132039 f x) = (term56 _132039 f x).
Proof. exact (eq_refl (term56 _132039 f x)). Qed.
Lemma lem7070935 {_132039 : Type'} (f : _132039 -> real) (g : _132039 -> real) (x : _132039) : (term57 _132039 f g x) = (term18 _132039 f g x).
Proof. exact (MK_COMB (@lem7070934 _132039 f x) (@lem7070933 _132039 g x)). Qed.
Lemma lem7070936 {_132039 : Type'} (f : _132039 -> real) (g : _132039 -> real) : (term58 _132039 f g) = (term20 _132039 f g).
Proof. exact (fun_ext (fun x : _132039 => @lem7070935 _132039 f g x)). Qed.
Lemma lem7070937 {_132039 : Type'} (s : _132039 -> Prop) : (@sum _132039 s) = (@sum _132039 s).
Proof. exact (eq_refl (@sum _132039 s)). Qed.
Lemma lem7070938 {_132039 : Type'} (s : _132039 -> Prop) (f : _132039 -> real) (g : _132039 -> real) : (term59 _132039 s f g) = (term22 _132039 s f g).
Proof. exact (MK_COMB (@lem7070937 _132039 s) (@lem7070936 _132039 f g)). Qed.
Lemma lem7070939 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7070940 {_132039 : Type'} (s : _132039 -> Prop) (f : _132039 -> real) (g : _132039 -> real) : (term60 _132039 s f g) = (term24 _132039 s f g).
Proof. exact (MK_COMB (@lem7070939) (@lem7070938 _132039 s f g)). Qed.
Lemma lem7070941 {_132039 : Type'} (f : _132039 -> real) (s : _132039 -> Prop) (g : _132039 -> real) : (term61 _132039 f s g) = (term61 _132039 f s g).
Proof. exact (eq_refl (term61 _132039 f s g)). Qed.
Lemma lem7070942 {_132039 : Type'} (f : _132039 -> real) (s : _132039 -> Prop) (g : _132039 -> real) : ((term59 _132039 s f g) = (term61 _132039 f s g)) = ((term22 _132039 s f g) = (term61 _132039 f s g)).
Proof. exact (MK_COMB (@lem7070940 _132039 s f g) (@lem7070941 _132039 f s g)). Qed.
Lemma lem7070943 {_132039 : Type'} (s : _132039 -> Prop) : (term27 _132039 s) = (term27 _132039 s).
Proof. exact (eq_refl (term27 _132039 s)). Qed.
Lemma lem7070944 {_132039 : Type'} (f : _132039 -> real) (s : _132039 -> Prop) (g : _132039 -> real) : (term52 _132039 f s g) = (term62 _132039 f s g).
Proof. exact (MK_COMB (@lem7070943 _132039 s) (@lem7070942 _132039 f s g)). Qed.
Lemma lem7070945 {_132039 : Type'} (f : _132039 -> real) (s : _132039 -> Prop) (g : _132039 -> real) : term62 _132039 f s g.
Proof. exact (EQ_MP (@lem7070944 _132039 f s g) (@lem7070932 _132039 f s g)). Qed.
Lemma lem7070947 {_132039 : Type'} (s : _132039 -> Prop) (h1 : @FINITE _132039 s) : (@FINITE _132039 s) = True.
Proof. exact (EQ_MP (@lem7070925 _132039 s) (@lem7070924 _132039 s h1)). Qed.
Lemma lem7070948 {_132039 : Type'} (s : _132039 -> Prop) (h1 : @FINITE _132039 s) : True = (@FINITE _132039 s).
Proof. exact (SYM (@lem7070947 _132039 s h1)). Qed.
Lemma lem7070949 {_132039 : Type'} (s : _132039 -> Prop) (h1 : @FINITE _132039 s) : @FINITE _132039 s.
Proof. exact (EQ_MP (@lem7070948 _132039 s h1) (@lem0)). Qed.
Lemma lem7070950 {_132039 : Type'} (f : _132039 -> real) (g : _132039 -> real) (s : _132039 -> Prop) (h1 : @FINITE _132039 s) : (term22 _132039 s f g) = (term61 _132039 f s g).
Proof. exact (@lem7070945 _132039 f s g (@lem7070949 _132039 s h1)). Qed.
Lemma lem7070952 {_132004 : Type'} (s : _132004 -> Prop) (f : _132004 -> real) : (term11 _132004 s f) = (term12 _132004 s f).
Proof. exact (EQ_MP (@lem7070848 _132004 s f) (@lem7070847 _132004 f s)). Qed.
Lemma lem7070953 {_132039 : Type'} (s : _132039 -> Prop) (f : _132039 -> real) : (term11 _132039 s f) = (term12 _132039 s f).
Proof. exact (@lem7070952 _132039 s f). Qed.
Lemma lem7070954 {_132039 : Type'} (s : _132039 -> Prop) (g : _132039 -> real) : (term11 _132039 s g) = (term12 _132039 s g).
Proof. exact (@lem7070953 _132039 s g). Qed.
Lemma lem7070955 {_132039 : Type'} (s : _132039 -> Prop) (f : _132039 -> real) : (term63 _132039 s f) = (term63 _132039 s f).
Proof. exact (eq_refl (term63 _132039 s f)). Qed.
Lemma lem7070956 {_132039 : Type'} (f : _132039 -> real) (s : _132039 -> Prop) (g : _132039 -> real) : (term61 _132039 f s g) = (term26 _132039 f s g).
Proof. exact (MK_COMB (@lem7070955 _132039 s f) (@lem7070954 _132039 s g)). Qed.
Lemma lem7070957 {_132039 : Type'} (f : _132039 -> real) (g : _132039 -> real) (s : _132039 -> Prop) (h1 : @FINITE _132039 s) : (term22 _132039 s f g) = (term26 _132039 f s g).
Proof. exact (TRANS (@lem7070950 _132039 f g s h1) (@lem7070956 _132039 f s g)). Qed.
Lemma lem7070958 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7070959 {_132039 : Type'} (f : _132039 -> real) (g : _132039 -> real) (s : _132039 -> Prop) (h1 : @FINITE _132039 s) : (term24 _132039 s f g) = (term64 _132039 f s g).
Proof. exact (MK_COMB (@lem7070958) (@lem7070957 _132039 f g s h1)). Qed.
Lemma lem7070960 {_132039 : Type'} (f : _132039 -> real) (s : _132039 -> Prop) (g : _132039 -> real) : (term26 _132039 f s g) = (term26 _132039 f s g).
Proof. exact (eq_refl (term26 _132039 f s g)). Qed.
Lemma lem7070961 {_132039 : Type'} (f : _132039 -> real) (g : _132039 -> real) (s : _132039 -> Prop) (h1 : @FINITE _132039 s) : ((term22 _132039 s f g) = (term26 _132039 f s g)) = ((term26 _132039 f s g) = (term26 _132039 f s g)).
Proof. exact (MK_COMB (@lem7070959 _132039 f g s h1) (@lem7070960 _132039 f s g)). Qed.
Lemma lem7070963 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7070964 (x : real) : (x = x) = True.
Proof. exact (@lem7070963 real x). Qed.
Lemma lem7070965 {_132039 : Type'} (f : _132039 -> real) (s : _132039 -> Prop) (g : _132039 -> real) : ((term26 _132039 f s g) = (term26 _132039 f s g)) = True.
Proof. exact (@lem7070964 (term26 _132039 f s g)). Qed.
Lemma lem7070966 {_132039 : Type'} (f : _132039 -> real) (g : _132039 -> real) (s : _132039 -> Prop) (h1 : @FINITE _132039 s) : ((term22 _132039 s f g) = (term26 _132039 f s g)) = True.
Proof. exact (TRANS (@lem7070961 _132039 f g s h1) (@lem7070965 _132039 f s g)). Qed.
Lemma lem7070967 {_132039 : Type'} (f : _132039 -> real) (s : _132039 -> Prop) (g : _132039 -> real) : term65 _132039 f s g.
Proof. exact (fun h0 : @FINITE _132039 s => @lem7070966 _132039 f g s h0). Qed.
Lemma lem7070968 {_132039 : Type'} (f : _132039 -> real) (g : _132039 -> real) (s : _132039 -> Prop) : term66 _132039 f g s.
Proof. exact (@lem7070923 _132039 f g s True). Qed.
Lemma lem7070969 {_132039 : Type'} (f : _132039 -> real) (g : _132039 -> real) (s : _132039 -> Prop) : (term29 _132039 f s g) = (term67 _132039 s).
Proof. exact (@lem7070968 _132039 f g s (@lem7070967 _132039 f s g)). Qed.
Lemma lem7070971 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7070972 {_132039 : Type'} (s : _132039 -> Prop) : (term67 _132039 s) = True.
Proof. exact (@lem7070971 (@FINITE _132039 s)). Qed.
Lemma lem7070973 {_132039 : Type'} (f : _132039 -> real) (s : _132039 -> Prop) (g : _132039 -> real) : (term29 _132039 f s g) = True.
Proof. exact (TRANS (@lem7070969 _132039 f g s) (@lem7070972 _132039 s)). Qed.
Lemma lem7070974 {_132039 : Type'} (f : _132039 -> real) (g : _132039 -> real) : (term31 _132039 f g) = (term68 _132039).
Proof. exact (fun_ext (fun s : _132039 -> Prop => @lem7070973 _132039 f s g)). Qed.
Lemma lem7070975 {_132039 : Type'} : (@all (_132039 -> Prop)) = (@all (_132039 -> Prop)).
Proof. exact (eq_refl (@all (_132039 -> Prop))). Qed.
Lemma lem7070976 {_132039 : Type'} (f : _132039 -> real) (g : _132039 -> real) : (term33 _132039 f g) = (term69 _132039).
Proof. exact (MK_COMB (@lem7070975 _132039) (@lem7070974 _132039 f g)). Qed.
Lemma lem7070978 {A : Type'} (t : Prop) : (term70 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7070979 {_132039 : Type'} (t : Prop) : (term71 _132039 t) = t.
Proof. exact (@lem7070978 (_132039 -> Prop) t). Qed.
Lemma lem7070980 {_132039 : Type'} : (term69 _132039) = True.
Proof. exact (@lem7070979 _132039 True). Qed.
Lemma lem7070981 {_132039 : Type'} (f : _132039 -> real) (g : _132039 -> real) : (term33 _132039 f g) = True.
Proof. exact (TRANS (@lem7070976 _132039 f g) (@lem7070980 _132039)). Qed.
Lemma lem7070982 {_132039 : Type'} (f : _132039 -> real) : (term35 _132039 f) = (term72 _132039).
Proof. exact (fun_ext (fun g : _132039 -> real => @lem7070981 _132039 f g)). Qed.
Lemma lem7070983 {_132039 : Type'} : (@all (_132039 -> real)) = (@all (_132039 -> real)).
Proof. exact (eq_refl (@all (_132039 -> real))). Qed.
Lemma lem7070984 {_132039 : Type'} (f : _132039 -> real) : (term37 _132039 f) = (term73 _132039).
Proof. exact (MK_COMB (@lem7070983 _132039) (@lem7070982 _132039 f)). Qed.
Lemma lem7070986 {A : Type'} (t : Prop) : (term70 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7070987 {_132039 : Type'} (t : Prop) : (term74 _132039 t) = t.
Proof. exact (@lem7070986 (_132039 -> real) t). Qed.
Lemma lem7070988 {_132039 : Type'} : (term73 _132039) = True.
Proof. exact (@lem7070987 _132039 True). Qed.
Lemma lem7070989 {_132039 : Type'} (f : _132039 -> real) : (term37 _132039 f) = True.
Proof. exact (TRANS (@lem7070984 _132039 f) (@lem7070988 _132039)). Qed.
Lemma lem7070990 {_132039 : Type'} : (term39 _132039) = (term72 _132039).
Proof. exact (fun_ext (fun f : _132039 -> real => @lem7070989 _132039 f)). Qed.
Lemma lem7070991 {_132039 : Type'} : (@all (_132039 -> real)) = (@all (_132039 -> real)).
Proof. exact (eq_refl (@all (_132039 -> real))). Qed.
Lemma lem7070992 {_132039 : Type'} : (term41 _132039) = (term73 _132039).
Proof. exact (MK_COMB (@lem7070991 _132039) (@lem7070990 _132039)). Qed.
Lemma lem7070994 {A : Type'} (t : Prop) : (term70 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7070995 {_132039 : Type'} (t : Prop) : (term74 _132039 t) = t.
Proof. exact (@lem7070994 (_132039 -> real) t). Qed.
Lemma lem7070996 {_132039 : Type'} : (term73 _132039) = True.
Proof. exact (@lem7070995 _132039 True). Qed.
Lemma lem7070997 {_132039 : Type'} : (term41 _132039) = True.
Proof. exact (TRANS (@lem7070992 _132039) (@lem7070996 _132039)). Qed.
Lemma lem7070998 {_132039 : Type'} : True = (term41 _132039).
Proof. exact (SYM (@lem7070997 _132039)). Qed.
Lemma lem7070999 {_132039 : Type'} : term41 _132039.
Proof. exact (EQ_MP (@lem7070998 _132039) (@lem0)). Qed.
Lemma lem7071000 {_132039 : Type'} : term40 _132039.
Proof. exact (EQ_MP (@lem7070895 _132039) (@lem7070999 _132039)). Qed.
