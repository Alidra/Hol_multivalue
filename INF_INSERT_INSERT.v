Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INF_INSERT_INSERT_term_abbrevs.
Require Import EXCLUDED_MIDDLE_spec.
Require Import FORALL_IN_INSERT_spec.
Require Import INF_EQ_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1365721_spec.
Require Import thm1367111_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1482698_spec.
Require Import thm1483429_spec.
Require Import thm17045_spec.
Require Import thm17646_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1843_spec.
Require Import thm1845_spec.
Require Import thm1857_spec.
Require Import thm19367_spec.
Require Import thm1980010_spec.
Require Import thm1980011_spec.
Require Import thm1980255_spec.
Require Import thm1980265_spec.
Require Import thm1980266_spec.
Require Import thm1981473_spec.
Require Import thm1981474_spec.
Require Import thm1981475_spec.
Require Import thm1981613_spec.
Require Import thm1982627_spec.
Require Import thm1982628_spec.
Require Import thm1982713_spec.
Require Import thm1982715_spec.
Require Import thm1982719_spec.
Require Import thm1982721_spec.
Require Import thm1982723_spec.
Require Import thm1982733_spec.
Require Import thm1982753_spec.
Require Import thm1982761_spec.
Require Import thm1982792_spec.
Require Import thm1988287_spec.
Require Import thm1988289_spec.
Require Import thm1988291_spec.
Require Import thm1988297_spec.
Require Import thm1988332_spec.
Require Import thm1988348_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem5256828 (s : real -> Prop) (c : real) : term0 s c.
Proof. exact (@lem9784 (term1 s c)). Qed.
Lemma lem5256829 (s : real -> Prop) (c : real) : (term0 s c) = (term2 s c).
Proof. exact (eq_refl (term0 s c)). Qed.
Lemma lem5256830 (s : real -> Prop) (c : real) : term2 s c.
Proof. exact (EQ_MP (@lem5256829 s c) (@lem5256828 s c)). Qed.
Lemma lem5256831 (s : real -> Prop) (c : real) (h1 : term1 s c) : term1 s c.
Proof. exact (h1). Qed.
Lemma lem5256832 (s : real -> Prop) (c : real) (h1 : term3 s c) : term3 s c.
Proof. exact (h1). Qed.
Lemma lem5256833 {_83983 : Type'} (P : _83983 -> Prop) : term4 _83983 P.
Proof. exact (@lem3207453 _83983 P). Qed.
Lemma lem5256834 {_83983 : Type'} (P : _83983 -> Prop) : (term4 _83983 P) = (term5 _83983 P).
Proof. exact (eq_refl (term4 _83983 P)). Qed.
Lemma lem5256835 {_83983 : Type'} (P : _83983 -> Prop) : term5 _83983 P.
Proof. exact (EQ_MP (@lem5256834 _83983 P) (@lem5256833 _83983 P)). Qed.
Lemma lem5256836 {_83983 : Type'} (P : _83983 -> Prop) (a : _83983) : term6 _83983 P a.
Proof. exact (@lem5256835 _83983 P a). Qed.
Lemma lem5256837 {_83983 : Type'} (a : _83983) (P : _83983 -> Prop) : (term6 _83983 P a) = (term7 _83983 a P).
Proof. exact (eq_refl (term6 _83983 P a)). Qed.
Lemma lem5256838 {_83983 : Type'} (a : _83983) (P : _83983 -> Prop) : term7 _83983 a P.
Proof. exact (EQ_MP (@lem5256837 _83983 a P) (@lem5256836 _83983 P a)). Qed.
Lemma lem5256839 {_83983 : Type'} (a : _83983) (P : _83983 -> Prop) (s : _83983 -> Prop) : term8 _83983 a P s.
Proof. exact (@lem5256838 _83983 a P s). Qed.
Lemma lem5256840 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term8 _83983 a P s) = ((term9 _83983 a s P) = (term10 _83983 a s P)).
Proof. exact (eq_refl (term8 _83983 a P s)). Qed.
Lemma lem5256842 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem5256843 (s : real -> Prop) (h1 : term11) : term12 s.
Proof. exact (@lem5256842 h1 s). Qed.
Lemma lem5256844 (s : real -> Prop) : (term12 s) = (term13 s).
Proof. exact (eq_refl (term12 s)). Qed.
Lemma lem5256845 (s : real -> Prop) (h1 : term11) : term13 s.
Proof. exact (EQ_MP (@lem5256844 s) (@lem5256843 s h1)). Qed.
Lemma lem5256846 (s : real -> Prop) (t : real -> Prop) (h1 : term11) : term14 s t.
Proof. exact (@lem5256845 s h1 t). Qed.
Lemma lem5256847 (s : real -> Prop) (t : real -> Prop) : (term14 s t) = (term15 s t).
Proof. exact (eq_refl (term14 s t)). Qed.
Lemma lem5256848 (s : real -> Prop) (t : real -> Prop) (h1 : term11) : term15 s t.
Proof. exact (EQ_MP (@lem5256847 s t) (@lem5256846 s t h1)). Qed.
Lemma lem5256849 (s : real -> Prop) (t : real -> Prop) (h1 : term16 s t) : term16 s t.
Proof. exact (h1). Qed.
Lemma lem5256850 (s : real -> Prop) (t : real -> Prop) (h1 : term11) (h2 : term16 s t) : (inf s) = (inf t).
Proof. exact (@lem5256848 s t h1 (@lem5256849 s t h2)). Qed.
Lemma lem5256851 (s : real -> Prop) (t : real -> Prop) (h1 : term16 s t) : term17 s t.
Proof. exact (fun h0 : term11 => @lem5256850 s t h0 h1). Qed.
Lemma lem5256852 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem5256853 (s : real -> Prop) (t : real -> Prop) (h1 : term11) (h2 : term16 s t) : (inf s) = (inf t).
Proof. exact (@lem5256851 s t h2 (@lem5256852 h1)). Qed.
Lemma lem5256854 (s : real -> Prop) (t : real -> Prop) (h1 : term11) : term15 s t.
Proof. exact (fun h0 : term16 s t => @lem5256853 s t h1 h0). Qed.
Lemma lem5256855 (s : real -> Prop) (h1 : term11) : term13 s.
Proof. exact (fun t : real -> Prop => @lem5256854 s t h1). Qed.
Lemma lem5256856 (h1 : term11) : term11.
Proof. exact (fun s : real -> Prop => @lem5256855 s h1). Qed.
Lemma lem5256857 : term18.
Proof. exact (fun h0 : term11 => @lem5256856 h0). Qed.
Lemma lem5256858 : term11.
Proof. exact (@lem5256857 (@lem5205408)). Qed.
Lemma lem5256859 (s : real -> Prop) : term12 s.
Proof. exact (@lem5256858 s). Qed.
Lemma lem5256860 (s : real -> Prop) : (term12 s) = (term13 s).
Proof. exact (eq_refl (term12 s)). Qed.
Lemma lem5256861 (s : real -> Prop) : term13 s.
Proof. exact (EQ_MP (@lem5256860 s) (@lem5256859 s)). Qed.
Lemma lem5256862 (s : real -> Prop) (t : real -> Prop) : term14 s t.
Proof. exact (@lem5256861 s t). Qed.
Lemma lem5256863 (s : real -> Prop) (t : real -> Prop) : (term14 s t) = (term15 s t).
Proof. exact (eq_refl (term14 s t)). Qed.
Lemma lem5256866 (s : real -> Prop) (t : real -> Prop) : term15 s t.
Proof. exact (EQ_MP (@lem5256863 s t) (@lem5256862 s t)). Qed.
Lemma lem5256867 (a : real) (b : real) (s : real -> Prop) : term19 a b s.
Proof. exact (@lem5256866 (term20 b a s) (term21 a b s)). Qed.
Lemma lem5256871 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term9 _83983 a s P) = (term10 _83983 a s P).
Proof. exact (EQ_MP (@lem5256840 _83983 a s P) (@lem5256839 _83983 a P s)). Qed.
Lemma lem5256872 (a : real) (s : real -> Prop) (P : real -> Prop) : (term22 a s P) = (term23 a s P).
Proof. exact (@lem5256871 real a s P). Qed.
Lemma lem5256873 (b : real) (a : real) (s : real -> Prop) (c : real) : (term24 b a s c) = (term25 b a s c).
Proof. exact (@lem5256872 b (@INSERT real a s) (term26 c)). Qed.
Lemma lem5256874 (c : real) (x : real) : (term27 c x) = (real_le c x).
Proof. exact (eq_refl (term27 c x)). Qed.
Lemma lem5256875 (x : real) (b : real) (a : real) (s : real -> Prop) : (term28 x b a s) = (term28 x b a s).
Proof. exact (eq_refl (term28 x b a s)). Qed.
Lemma lem5256876 (b : real) (a : real) (s : real -> Prop) (c : real) (x : real) : (term29 b a s c x) = (term30 b a s c x).
Proof. exact (MK_COMB (@lem5256875 x b a s) (@lem5256874 c x)). Qed.
Lemma lem5256877 (b : real) (a : real) (s : real -> Prop) (c : real) : (term31 b a s c) = (term32 b a s c).
Proof. exact (fun_ext (fun x : real => @lem5256876 b a s c x)). Qed.
Lemma lem5256878 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5256879 (b : real) (a : real) (s : real -> Prop) (c : real) : (term24 b a s c) = (term33 b a s c).
Proof. exact (MK_COMB (@lem5256878) (@lem5256877 b a s c)). Qed.
Lemma lem5256880 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5256881 (b : real) (a : real) (s : real -> Prop) (c : real) : (term34 b a s c) = (term35 b a s c).
Proof. exact (MK_COMB (@lem5256880) (@lem5256879 b a s c)). Qed.
Lemma lem5256882 (c : real) (b : real) : (term27 c b) = (real_le c b).
Proof. exact (eq_refl (term27 c b)). Qed.
Lemma lem5256883 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5256884 (c : real) (b : real) : (term36 c b) = (term37 c b).
Proof. exact (MK_COMB (@lem5256883) (@lem5256882 c b)). Qed.
Lemma lem5256885 (c : real) (x : real) : (term27 c x) = (real_le c x).
Proof. exact (eq_refl (term27 c x)). Qed.
Lemma lem5256886 (x : real) (a : real) (s : real -> Prop) : (term38 x a s) = (term38 x a s).
Proof. exact (eq_refl (term38 x a s)). Qed.
Lemma lem5256887 (a : real) (s : real -> Prop) (c : real) (x : real) : (term39 a s c x) = (term40 a s c x).
Proof. exact (MK_COMB (@lem5256886 x a s) (@lem5256885 c x)). Qed.
Lemma lem5256888 (a : real) (s : real -> Prop) (c : real) : (term41 a s c) = (term42 a s c).
Proof. exact (fun_ext (fun x : real => @lem5256887 a s c x)). Qed.
Lemma lem5256889 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5256890 (a : real) (s : real -> Prop) (c : real) : (term43 a s c) = (term44 a s c).
Proof. exact (MK_COMB (@lem5256889) (@lem5256888 a s c)). Qed.
Lemma lem5256891 (b : real) (a : real) (s : real -> Prop) (c : real) : (term25 b a s c) = (term45 b a s c).
Proof. exact (MK_COMB (@lem5256884 c b) (@lem5256890 a s c)). Qed.
Lemma lem5256892 (b : real) (a : real) (s : real -> Prop) (c : real) : ((term24 b a s c) = (term25 b a s c)) = ((term33 b a s c) = (term45 b a s c)).
Proof. exact (MK_COMB (@lem5256881 b a s c) (@lem5256891 b a s c)). Qed.
Lemma lem5256893 (b : real) (a : real) (s : real -> Prop) (c : real) : (term33 b a s c) = (term45 b a s c).
Proof. exact (EQ_MP (@lem5256892 b a s c) (@lem5256873 b a s c)). Qed.
Lemma lem5256897 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term9 _83983 a s P) = (term10 _83983 a s P).
Proof. exact (EQ_MP (@lem5256840 _83983 a s P) (@lem5256839 _83983 a P s)). Qed.
Lemma lem5256898 (a : real) (s : real -> Prop) (P : real -> Prop) : (term22 a s P) = (term23 a s P).
Proof. exact (@lem5256897 real a s P). Qed.
Lemma lem5256899 (a : real) (s : real -> Prop) (c : real) : (term43 a s c) = (term46 a s c).
Proof. exact (@lem5256898 a s (term26 c)). Qed.
Lemma lem5256900 (c : real) (x : real) : (term27 c x) = (real_le c x).
Proof. exact (eq_refl (term27 c x)). Qed.
Lemma lem5256901 (x : real) (a : real) (s : real -> Prop) : (term38 x a s) = (term38 x a s).
Proof. exact (eq_refl (term38 x a s)). Qed.
Lemma lem5256902 (a : real) (s : real -> Prop) (c : real) (x : real) : (term39 a s c x) = (term40 a s c x).
Proof. exact (MK_COMB (@lem5256901 x a s) (@lem5256900 c x)). Qed.
Lemma lem5256903 (a : real) (s : real -> Prop) (c : real) : (term41 a s c) = (term42 a s c).
Proof. exact (fun_ext (fun x : real => @lem5256902 a s c x)). Qed.
Lemma lem5256904 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5256905 (a : real) (s : real -> Prop) (c : real) : (term43 a s c) = (term44 a s c).
Proof. exact (MK_COMB (@lem5256904) (@lem5256903 a s c)). Qed.
Lemma lem5256906 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5256907 (a : real) (s : real -> Prop) (c : real) : (term47 a s c) = (term48 a s c).
Proof. exact (MK_COMB (@lem5256906) (@lem5256905 a s c)). Qed.
Lemma lem5256908 (c : real) (a : real) : (term27 c a) = (real_le c a).
Proof. exact (eq_refl (term27 c a)). Qed.
Lemma lem5256909 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5256910 (c : real) (a : real) : (term36 c a) = (term37 c a).
Proof. exact (MK_COMB (@lem5256909) (@lem5256908 c a)). Qed.
Lemma lem5256911 (c : real) (x : real) : (term27 c x) = (real_le c x).
Proof. exact (eq_refl (term27 c x)). Qed.
Lemma lem5256912 (x : real) (s : real -> Prop) : (term49 x s) = (term49 x s).
Proof. exact (eq_refl (term49 x s)). Qed.
Lemma lem5256913 (s : real -> Prop) (c : real) (x : real) : (term50 s c x) = (term51 s c x).
Proof. exact (MK_COMB (@lem5256912 x s) (@lem5256911 c x)). Qed.
Lemma lem5256914 (s : real -> Prop) (c : real) : (term52 s c) = (term53 s c).
Proof. exact (fun_ext (fun x : real => @lem5256913 s c x)). Qed.
Lemma lem5256915 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5256916 (s : real -> Prop) (c : real) : (term54 s c) = (term1 s c).
Proof. exact (MK_COMB (@lem5256915) (@lem5256914 s c)). Qed.
Lemma lem5256917 (a : real) (s : real -> Prop) (c : real) : (term46 a s c) = (term55 a s c).
Proof. exact (MK_COMB (@lem5256910 c a) (@lem5256916 s c)). Qed.
Lemma lem5256918 (a : real) (s : real -> Prop) (c : real) : ((term43 a s c) = (term46 a s c)) = ((term44 a s c) = (term55 a s c)).
Proof. exact (MK_COMB (@lem5256907 a s c) (@lem5256917 a s c)). Qed.
Lemma lem5256919 (a : real) (s : real -> Prop) (c : real) : (term44 a s c) = (term55 a s c).
Proof. exact (EQ_MP (@lem5256918 a s c) (@lem5256899 a s c)). Qed.
Lemma lem5256928 (c : real) (b : real) : (term37 c b) = (term37 c b).
Proof. exact (eq_refl (term37 c b)). Qed.
Lemma lem5256929 (b : real) (a : real) (s : real -> Prop) (c : real) : (term45 b a s c) = (term56 b a s c).
Proof. exact (MK_COMB (@lem5256928 c b) (@lem5256919 a s c)). Qed.
Lemma lem5256932 (b : real) (a : real) (s : real -> Prop) (c : real) : (term33 b a s c) = (term56 b a s c).
Proof. exact (TRANS (@lem5256893 b a s c) (@lem5256929 b a s c)). Qed.
Lemma lem5256933 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5256934 (b : real) (a : real) (s : real -> Prop) (c : real) : (term35 b a s c) = (term57 b a s c).
Proof. exact (MK_COMB (@lem5256933) (@lem5256932 b a s c)). Qed.
Lemma lem5256936 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term9 _83983 a s P) = (term10 _83983 a s P).
Proof. exact (EQ_MP (@lem5256840 _83983 a s P) (@lem5256839 _83983 a P s)). Qed.
Lemma lem5256937 (a : real) (s : real -> Prop) (P : real -> Prop) : (term22 a s P) = (term23 a s P).
Proof. exact (@lem5256936 real a s P). Qed.
Lemma lem5256938 (a : real) (b : real) (s : real -> Prop) (c : real) : (term58 a b s c) = (term59 a b s c).
Proof. exact (@lem5256937 (real_min a b) s (term26 c)). Qed.
Lemma lem5256939 (c : real) (x : real) : (term27 c x) = (real_le c x).
Proof. exact (eq_refl (term27 c x)). Qed.
Lemma lem5256940 (x : real) (a : real) (b : real) (s : real -> Prop) : (term60 x a b s) = (term60 x a b s).
Proof. exact (eq_refl (term60 x a b s)). Qed.
Lemma lem5256941 (a : real) (b : real) (s : real -> Prop) (c : real) (x : real) : (term61 a b s c x) = (term62 a b s c x).
Proof. exact (MK_COMB (@lem5256940 x a b s) (@lem5256939 c x)). Qed.
Lemma lem5256942 (a : real) (b : real) (s : real -> Prop) (c : real) : (term63 a b s c) = (term64 a b s c).
Proof. exact (fun_ext (fun x : real => @lem5256941 a b s c x)). Qed.
Lemma lem5256943 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5256944 (a : real) (b : real) (s : real -> Prop) (c : real) : (term58 a b s c) = (term65 a b s c).
Proof. exact (MK_COMB (@lem5256943) (@lem5256942 a b s c)). Qed.
Lemma lem5256945 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5256946 (a : real) (b : real) (s : real -> Prop) (c : real) : (term66 a b s c) = (term67 a b s c).
Proof. exact (MK_COMB (@lem5256945) (@lem5256944 a b s c)). Qed.
Lemma lem5256947 (c : real) (a : real) (b : real) : (term68 c a b) = (term69 c a b).
Proof. exact (eq_refl (term68 c a b)). Qed.
Lemma lem5256948 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5256949 (c : real) (a : real) (b : real) : (term70 c a b) = (term71 c a b).
Proof. exact (MK_COMB (@lem5256948) (@lem5256947 c a b)). Qed.
Lemma lem5256950 (c : real) (x : real) : (term27 c x) = (real_le c x).
Proof. exact (eq_refl (term27 c x)). Qed.
Lemma lem5256951 (x : real) (s : real -> Prop) : (term49 x s) = (term49 x s).
Proof. exact (eq_refl (term49 x s)). Qed.
Lemma lem5256952 (s : real -> Prop) (c : real) (x : real) : (term50 s c x) = (term51 s c x).
Proof. exact (MK_COMB (@lem5256951 x s) (@lem5256950 c x)). Qed.
Lemma lem5256953 (s : real -> Prop) (c : real) : (term52 s c) = (term53 s c).
Proof. exact (fun_ext (fun x : real => @lem5256952 s c x)). Qed.
Lemma lem5256954 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5256955 (s : real -> Prop) (c : real) : (term54 s c) = (term1 s c).
Proof. exact (MK_COMB (@lem5256954) (@lem5256953 s c)). Qed.
Lemma lem5256956 (a : real) (b : real) (s : real -> Prop) (c : real) : (term59 a b s c) = (term72 a b s c).
Proof. exact (MK_COMB (@lem5256949 c a b) (@lem5256955 s c)). Qed.
Lemma lem5256957 (a : real) (b : real) (s : real -> Prop) (c : real) : ((term58 a b s c) = (term59 a b s c)) = ((term65 a b s c) = (term72 a b s c)).
Proof. exact (MK_COMB (@lem5256946 a b s c) (@lem5256956 a b s c)). Qed.
Lemma lem5256958 (a : real) (b : real) (s : real -> Prop) (c : real) : (term65 a b s c) = (term72 a b s c).
Proof. exact (EQ_MP (@lem5256957 a b s c) (@lem5256938 a b s c)). Qed.
Lemma lem5256967 (a : real) (b : real) (s : real -> Prop) (c : real) : ((term33 b a s c) = (term65 a b s c)) = ((term56 b a s c) = (term72 a b s c)).
Proof. exact (MK_COMB (@lem5256934 b a s c) (@lem5256958 a b s c)). Qed.
Lemma lem5256970 (a : real) (b : real) (s : real -> Prop) (c : real) : ((term56 b a s c) = (term72 a b s c)) = ((term33 b a s c) = (term65 a b s c)).
Proof. exact (SYM (@lem5256967 a b s c)). Qed.
Lemma lem5256971 (x : real) (s : real -> Prop) (c : real) (h1 : term1 s c) : term73 s c x.
Proof. exact (@lem5256831 s c h1 x). Qed.
Lemma lem5256972 (s : real -> Prop) (c : real) (x : real) : (term73 s c x) = (term51 s c x).
Proof. exact (eq_refl (term73 s c x)). Qed.
Lemma lem5256973 (x : real) (s : real -> Prop) (c : real) (h1 : term1 s c) : term51 s c x.
Proof. exact (EQ_MP (@lem5256972 s c x) (@lem5256971 x s c h1)). Qed.
Lemma lem5256974 (s : real -> Prop) (c : real) (x : real) : (term51 s c x) = ((term51 s c x) = True).
Proof. exact (@lem7 (term51 s c x)). Qed.
Lemma lem5256987 (x : real) (s : real -> Prop) (c : real) (h1 : term1 s c) : (term51 s c x) = True.
Proof. exact (EQ_MP (@lem5256974 s c x) (@lem5256973 x s c h1)). Qed.
Lemma lem5256988 (s : real -> Prop) (c : real) (h1 : term1 s c) : (term53 s c) = term74.
Proof. exact (fun_ext (fun x : real => @lem5256987 x s c h1)). Qed.
Lemma lem5256989 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5256990 (s : real -> Prop) (c : real) (h1 : term1 s c) : (term1 s c) = term75.
Proof. exact (MK_COMB (@lem5256989) (@lem5256988 s c h1)). Qed.
Lemma lem5256992 {A : Type'} (t : Prop) : (term76 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5256993 (t : Prop) : (term77 t) = t.
Proof. exact (@lem5256992 real t). Qed.
Lemma lem5256994 : term75 = True.
Proof. exact (@lem5256993 True). Qed.
Lemma lem5256995 (s : real -> Prop) (c : real) (h1 : term1 s c) : (term1 s c) = True.
Proof. exact (TRANS (@lem5256990 s c h1) (@lem5256994)). Qed.
Lemma lem5256996 (c : real) (a : real) : (term37 c a) = (term37 c a).
Proof. exact (eq_refl (term37 c a)). Qed.
Lemma lem5256997 (a : real) (s : real -> Prop) (c : real) (h1 : term1 s c) : (term55 a s c) = (term78 c a).
Proof. exact (MK_COMB (@lem5256996 c a) (@lem5256995 s c h1)). Qed.
Lemma lem5256999 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem5257000 (c : real) (a : real) : (term78 c a) = (real_le c a).
Proof. exact (@lem5256999 (real_le c a)). Qed.
Lemma lem5257001 (a : real) (s : real -> Prop) (c : real) (h1 : term1 s c) : (term55 a s c) = (real_le c a).
Proof. exact (TRANS (@lem5256997 a s c h1) (@lem5257000 c a)). Qed.
Lemma lem5257002 (c : real) (b : real) : (term37 c b) = (term37 c b).
Proof. exact (eq_refl (term37 c b)). Qed.
Lemma lem5257003 (b : real) (a : real) (s : real -> Prop) (c : real) (h1 : term1 s c) : (term56 b a s c) = (term79 b c a).
Proof. exact (MK_COMB (@lem5257002 c b) (@lem5257001 a s c h1)). Qed.
Lemma lem5257006 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5257007 (b : real) (a : real) (s : real -> Prop) (c : real) (h1 : term1 s c) : (term57 b a s c) = (term80 b c a).
Proof. exact (MK_COMB (@lem5257006) (@lem5257003 b a s c h1)). Qed.
Lemma lem5257015 (x : real) (s : real -> Prop) (c : real) (h1 : term1 s c) : (term51 s c x) = True.
Proof. exact (EQ_MP (@lem5256974 s c x) (@lem5256973 x s c h1)). Qed.
Lemma lem5257016 (s : real -> Prop) (c : real) (h1 : term1 s c) : (term53 s c) = term74.
Proof. exact (fun_ext (fun x : real => @lem5257015 x s c h1)). Qed.
Lemma lem5257017 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5257018 (s : real -> Prop) (c : real) (h1 : term1 s c) : (term1 s c) = term75.
Proof. exact (MK_COMB (@lem5257017) (@lem5257016 s c h1)). Qed.
Lemma lem5257020 {A : Type'} (t : Prop) : (term76 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5257021 (t : Prop) : (term77 t) = t.
Proof. exact (@lem5257020 real t). Qed.
Lemma lem5257022 : term75 = True.
Proof. exact (@lem5257021 True). Qed.
Lemma lem5257023 (s : real -> Prop) (c : real) (h1 : term1 s c) : (term1 s c) = True.
Proof. exact (TRANS (@lem5257018 s c h1) (@lem5257022)). Qed.
Lemma lem5257024 (c : real) (a : real) (b : real) : (term71 c a b) = (term71 c a b).
Proof. exact (eq_refl (term71 c a b)). Qed.
Lemma lem5257025 (a : real) (b : real) (s : real -> Prop) (c : real) (h1 : term1 s c) : (term72 a b s c) = (term81 c a b).
Proof. exact (MK_COMB (@lem5257024 c a b) (@lem5257023 s c h1)). Qed.
Lemma lem5257027 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem5257028 (c : real) (a : real) (b : real) : (term81 c a b) = (term69 c a b).
Proof. exact (@lem5257027 (term69 c a b)). Qed.
Lemma lem5257029 (a : real) (b : real) (s : real -> Prop) (c : real) (h1 : term1 s c) : (term72 a b s c) = (term69 c a b).
Proof. exact (TRANS (@lem5257025 a b s c h1) (@lem5257028 c a b)). Qed.
Lemma lem5257030 (a : real) (b : real) (s : real -> Prop) (c : real) (h1 : term1 s c) : ((term56 b a s c) = (term72 a b s c)) = ((term79 b c a) = (term69 c a b)).
Proof. exact (MK_COMB (@lem5257007 b a s c h1) (@lem5257029 a b s c h1)). Qed.
Lemma lem5257033 (a : real) (b : real) (s : real -> Prop) (c : real) (h1 : term1 s c) : ((term79 b c a) = (term69 c a b)) = ((term56 b a s c) = (term72 a b s c)).
Proof. exact (SYM (@lem5257030 a b s c h1)). Qed.
Lemma lem5257034 (s : real -> Prop) (c : real) : term82 s c.
Proof. exact (@lem82 (term1 s c)). Qed.
Lemma lem5257043 (s : real -> Prop) (c : real) (h1 : term3 s c) : (term1 s c) = False.
Proof. exact (@lem5257034 s c (@lem5256832 s c h1)). Qed.
Lemma lem5257044 (c : real) (a : real) : (term37 c a) = (term37 c a).
Proof. exact (eq_refl (term37 c a)). Qed.
Lemma lem5257045 (a : real) (s : real -> Prop) (c : real) (h1 : term3 s c) : (term55 a s c) = (term83 c a).
Proof. exact (MK_COMB (@lem5257044 c a) (@lem5257043 s c h1)). Qed.
Lemma lem5257047 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem5257048 (c : real) (a : real) : (term83 c a) = False.
Proof. exact (@lem5257047 (real_le c a)). Qed.
Lemma lem5257049 (a : real) (s : real -> Prop) (c : real) (h1 : term3 s c) : (term55 a s c) = False.
Proof. exact (TRANS (@lem5257045 a s c h1) (@lem5257048 c a)). Qed.
Lemma lem5257050 (c : real) (b : real) : (term37 c b) = (term37 c b).
Proof. exact (eq_refl (term37 c b)). Qed.
Lemma lem5257051 (a : real) (b : real) (s : real -> Prop) (c : real) (h1 : term3 s c) : (term56 b a s c) = (term83 c b).
Proof. exact (MK_COMB (@lem5257050 c b) (@lem5257049 a s c h1)). Qed.
Lemma lem5257053 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem5257054 (c : real) (b : real) : (term83 c b) = False.
Proof. exact (@lem5257053 (real_le c b)). Qed.
Lemma lem5257055 (b : real) (a : real) (s : real -> Prop) (c : real) (h1 : term3 s c) : (term56 b a s c) = False.
Proof. exact (TRANS (@lem5257051 a b s c h1) (@lem5257054 c b)). Qed.
Lemma lem5257056 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5257057 (b : real) (a : real) (s : real -> Prop) (c : real) (h1 : term3 s c) : (term57 b a s c) = (@eq Prop False).
Proof. exact (MK_COMB (@lem5257056) (@lem5257055 b a s c h1)). Qed.
Lemma lem5257061 (s : real -> Prop) (c : real) (h1 : term3 s c) : (term1 s c) = False.
Proof. exact (@lem5257034 s c (@lem5256832 s c h1)). Qed.
Lemma lem5257062 (c : real) (a : real) (b : real) : (term71 c a b) = (term71 c a b).
Proof. exact (eq_refl (term71 c a b)). Qed.
Lemma lem5257063 (a : real) (b : real) (s : real -> Prop) (c : real) (h1 : term3 s c) : (term72 a b s c) = (term84 c a b).
Proof. exact (MK_COMB (@lem5257062 c a b) (@lem5257061 s c h1)). Qed.
Lemma lem5257065 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem5257066 (c : real) (a : real) (b : real) : (term84 c a b) = False.
Proof. exact (@lem5257065 (term69 c a b)). Qed.
Lemma lem5257067 (a : real) (b : real) (s : real -> Prop) (c : real) (h1 : term3 s c) : (term72 a b s c) = False.
Proof. exact (TRANS (@lem5257063 a b s c h1) (@lem5257066 c a b)). Qed.
Lemma lem5257068 (a : real) (b : real) (s : real -> Prop) (c : real) (h1 : term3 s c) : ((term56 b a s c) = (term72 a b s c)) = (False = False).
Proof. exact (MK_COMB (@lem5257057 b a s c h1) (@lem5257067 a b s c h1)). Qed.
Lemma lem5257070 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem5257071 : (False = False) = (~ False).
Proof. exact (@lem5257070 False). Qed.
Lemma lem5257073 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem5257074 : (False = False) = True.
Proof. exact (TRANS (@lem5257071) (@lem5257073)). Qed.
Lemma lem5257075 (a : real) (b : real) (s : real -> Prop) (c : real) (h1 : term3 s c) : ((term56 b a s c) = (term72 a b s c)) = True.
Proof. exact (TRANS (@lem5257068 a b s c h1) (@lem5257074)). Qed.
Lemma lem5257076 (a : real) (b : real) (s : real -> Prop) (c : real) (h1 : term3 s c) : True = ((term56 b a s c) = (term72 a b s c)).
Proof. exact (SYM (@lem5257075 a b s c h1)). Qed.
Lemma lem5257077 (a : real) (b : real) (s : real -> Prop) (c : real) (h1 : term3 s c) : (term56 b a s c) = (term72 a b s c).
Proof. exact (EQ_MP (@lem5257076 a b s c h1) (@lem0)). Qed.
Lemma lem5257092 (b : real) (c : real) (a : real) : (term85 b c a) = (term86 b c a).
Proof. exact (@lem17045 (real_le c b) (real_le c a)). Qed.
Lemma lem5257097 (c : real) (a : real) (b : real) : (term69 c a b) = (term69 c a b).
Proof. exact (eq_refl (term69 c a b)). Qed.
Lemma lem5257098 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5257099 (b : real) (c : real) (a : real) : (term87 b c a) = (term88 b c a).
Proof. exact (MK_COMB (@lem5257098) (@lem5257092 b c a)). Qed.
Lemma lem5257100 (c : real) (a : real) (b : real) : (term89 c a b) = (term90 c a b).
Proof. exact (MK_COMB (@lem5257099 b c a) (@lem5257097 c a b)). Qed.
Lemma lem5257105 (c : real) (a : real) (b : real) : (term91 c a b) = (term91 c a b).
Proof. exact (eq_refl (term91 c a b)). Qed.
Lemma lem5257106 (c : real) (a : real) (b : real) : (term92 c a b) = (term93 c a b).
Proof. exact (MK_COMB (@lem5257105 c a b) (@lem5257100 c a b)). Qed.
Lemma lem5257107 (c : real) (a : real) (b : real) : (term94 c a b) = (term92 c a b).
Proof. exact (@lem17646 (term79 b c a) (term69 c a b)). Qed.
Lemma lem5257137 (c : real) (a : real) (b : real) : (term94 c a b) = (term93 c a b).
Proof. exact (TRANS (@lem5257107 c a b) (@lem5257106 c a b)). Qed.
Lemma lem5257138 (b : real) (c : real) : (real_le c b) = (term95 b c).
Proof. exact (@lem1988287 b c). Qed.
Lemma lem5257151 (b : real) (c : real) : (real_sub b c) = (term96 b c).
Proof. exact (@lem1982792 b c). Qed.
Lemma lem5257152 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5257153 (b : real) (c : real) : (term97 b c) = (term98 b c).
Proof. exact (MK_COMB (@lem5257152) (@lem5257151 b c)). Qed.
Lemma lem5257154 : term99 = term99.
Proof. exact (eq_refl term99). Qed.
Lemma lem5257155 (b : real) (c : real) : (term95 b c) = (term100 b c).
Proof. exact (MK_COMB (@lem5257153 b c) (@lem5257154)). Qed.
Lemma lem5257156 (b : real) (c : real) : (real_le c b) = (term100 b c).
Proof. exact (TRANS (@lem5257138 b c) (@lem5257155 b c)). Qed.
Lemma lem5257157 (a : real) (c : real) : (real_le c a) = (term95 a c).
Proof. exact (@lem1988287 a c). Qed.
Lemma lem5257170 (a : real) (c : real) : (real_sub a c) = (term96 a c).
Proof. exact (@lem1982792 a c). Qed.
Lemma lem5257171 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5257172 (a : real) (c : real) : (term97 a c) = (term98 a c).
Proof. exact (MK_COMB (@lem5257171) (@lem5257170 a c)). Qed.
Lemma lem5257173 : term99 = term99.
Proof. exact (eq_refl term99). Qed.
Lemma lem5257174 (a : real) (c : real) : (term95 a c) = (term100 a c).
Proof. exact (MK_COMB (@lem5257172 a c) (@lem5257173)). Qed.
Lemma lem5257175 (a : real) (c : real) : (real_le c a) = (term100 a c).
Proof. exact (TRANS (@lem5257157 a c) (@lem5257174 a c)). Qed.
Lemma lem5257176 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5257177 (b : real) (c : real) : (term37 c b) = (term101 b c).
Proof. exact (MK_COMB (@lem5257176) (@lem5257156 b c)). Qed.
Lemma lem5257178 (b : real) (a : real) (c : real) : (term79 b c a) = (term102 b a c).
Proof. exact (MK_COMB (@lem5257177 b c) (@lem5257175 a c)). Qed.
Lemma lem5257179 (c : real) (a : real) (b : real) : (term103 c a b) = (term104 c a b).
Proof. exact (@lem1988297 c (real_min a b)). Qed.
Lemma lem5257196 (c : real) (a : real) (b : real) : (term105 c a b) = (term106 c a b).
Proof. exact (@lem1982792 c (real_min a b)). Qed.
Lemma lem5257197 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5257198 (c : real) (a : real) (b : real) : (term107 c a b) = (term108 c a b).
Proof. exact (MK_COMB (@lem5257197) (@lem5257196 c a b)). Qed.
Lemma lem5257199 : term99 = term99.
Proof. exact (eq_refl term99). Qed.
Lemma lem5257200 (c : real) (a : real) (b : real) : (term104 c a b) = (term109 c a b).
Proof. exact (MK_COMB (@lem5257198 c a b) (@lem5257199)). Qed.
Lemma lem5257201 (c : real) (a : real) (b : real) : (term103 c a b) = (term109 c a b).
Proof. exact (TRANS (@lem5257179 c a b) (@lem5257200 c a b)). Qed.
Lemma lem5257202 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5257203 (b : real) (a : real) (c : real) : (term110 b c a) = (term111 b a c).
Proof. exact (MK_COMB (@lem5257202) (@lem5257178 b a c)). Qed.
Lemma lem5257204 (c : real) (a : real) (b : real) : (term112 c a b) = (term113 c a b).
Proof. exact (MK_COMB (@lem5257203 b a c) (@lem5257201 c a b)). Qed.
Lemma lem5257205 (c : real) (b : real) : (term114 c b) = (term115 c b).
Proof. exact (@lem1988297 c b). Qed.
Lemma lem5257211 (c : real) (b : real) : (real_sub c b) = (term96 c b).
Proof. exact (@lem1982792 c b). Qed.
Lemma lem5257216 (b : real) (c : real) : (term96 c b) = (term116 b c).
Proof. exact (@lem1982761 (term117 b) c). Qed.
Lemma lem5257218 (b : real) (c : real) : (real_sub c b) = (term116 b c).
Proof. exact (TRANS (@lem5257211 c b) (@lem5257216 b c)). Qed.
Lemma lem5257219 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5257220 (b : real) (c : real) : (term118 c b) = (term119 b c).
Proof. exact (MK_COMB (@lem5257219) (@lem5257218 b c)). Qed.
Lemma lem5257221 : term99 = term99.
Proof. exact (eq_refl term99). Qed.
Lemma lem5257222 (b : real) (c : real) : (term115 c b) = (term120 b c).
Proof. exact (MK_COMB (@lem5257220 b c) (@lem5257221)). Qed.
Lemma lem5257223 (b : real) (c : real) : (term114 c b) = (term120 b c).
Proof. exact (TRANS (@lem5257205 c b) (@lem5257222 b c)). Qed.
Lemma lem5257224 (c : real) (a : real) : (term114 c a) = (term115 c a).
Proof. exact (@lem1988297 c a). Qed.
Lemma lem5257230 (c : real) (a : real) : (real_sub c a) = (term96 c a).
Proof. exact (@lem1982792 c a). Qed.
Lemma lem5257235 (a : real) (c : real) : (term96 c a) = (term116 a c).
Proof. exact (@lem1982761 (term117 a) c). Qed.
Lemma lem5257237 (a : real) (c : real) : (real_sub c a) = (term116 a c).
Proof. exact (TRANS (@lem5257230 c a) (@lem5257235 a c)). Qed.
Lemma lem5257238 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5257239 (a : real) (c : real) : (term118 c a) = (term119 a c).
Proof. exact (MK_COMB (@lem5257238) (@lem5257237 a c)). Qed.
Lemma lem5257240 : term99 = term99.
Proof. exact (eq_refl term99). Qed.
Lemma lem5257241 (a : real) (c : real) : (term115 c a) = (term120 a c).
Proof. exact (MK_COMB (@lem5257239 a c) (@lem5257240)). Qed.
Lemma lem5257242 (a : real) (c : real) : (term114 c a) = (term120 a c).
Proof. exact (TRANS (@lem5257224 c a) (@lem5257241 a c)). Qed.
Lemma lem5257243 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5257244 (b : real) (c : real) : (term121 c b) = (term122 b c).
Proof. exact (MK_COMB (@lem5257243) (@lem5257223 b c)). Qed.
Lemma lem5257245 (b : real) (a : real) (c : real) : (term86 b c a) = (term123 b a c).
Proof. exact (MK_COMB (@lem5257244 b c) (@lem5257242 a c)). Qed.
Lemma lem5257246 (a : real) (b : real) (c : real) : (term69 c a b) = (term124 a b c).
Proof. exact (@lem1988287 (real_min a b) c). Qed.
Lemma lem5257256 (a : real) (b : real) (c : real) : (term125 a b c) = (term126 a b c).
Proof. exact (@lem1982792 (real_min a b) c). Qed.
Lemma lem5257261 (c : real) (a : real) (b : real) : (term126 a b c) = (term127 c a b).
Proof. exact (@lem1982761 (term117 c) (real_min a b)). Qed.
Lemma lem5257263 (c : real) (a : real) (b : real) : (term125 a b c) = (term127 c a b).
Proof. exact (TRANS (@lem5257256 a b c) (@lem5257261 c a b)). Qed.
Lemma lem5257264 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5257265 (c : real) (a : real) (b : real) : (term128 a b c) = (term129 c a b).
Proof. exact (MK_COMB (@lem5257264) (@lem5257263 c a b)). Qed.
Lemma lem5257266 : term99 = term99.
Proof. exact (eq_refl term99). Qed.
Lemma lem5257267 (c : real) (a : real) (b : real) : (term124 a b c) = (term130 c a b).
Proof. exact (MK_COMB (@lem5257265 c a b) (@lem5257266)). Qed.
Lemma lem5257268 (c : real) (a : real) (b : real) : (term69 c a b) = (term130 c a b).
Proof. exact (TRANS (@lem5257246 a b c) (@lem5257267 c a b)). Qed.
Lemma lem5257269 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5257270 (b : real) (a : real) (c : real) : (term88 b c a) = (term131 b a c).
Proof. exact (MK_COMB (@lem5257269) (@lem5257245 b a c)). Qed.
Lemma lem5257271 (c : real) (a : real) (b : real) : (term90 c a b) = (term132 c a b).
Proof. exact (MK_COMB (@lem5257270 b a c) (@lem5257268 c a b)). Qed.
Lemma lem5257272 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5257273 (c : real) (a : real) (b : real) : (term91 c a b) = (term133 c a b).
Proof. exact (MK_COMB (@lem5257272) (@lem5257204 c a b)). Qed.
Lemma lem5257274 (c : real) (a : real) (b : real) : (term93 c a b) = (term134 c a b).
Proof. exact (MK_COMB (@lem5257273 c a b) (@lem5257271 c a b)). Qed.
Lemma lem5257281 (c : real) (a : real) (b : real) : (term94 c a b) = (term134 c a b).
Proof. exact (TRANS (@lem5257137 c a b) (@lem5257274 c a b)). Qed.
Lemma lem5257298 (c : real) (a : real) (b : real) : (term132 c a b) = (term135 c a b).
Proof. exact (@lem19367 (term120 b c) (term120 a c) (term130 c a b)). Qed.
Lemma lem5257313 (c : real) (a : real) (b : real) : (term133 c a b) = (term133 c a b).
Proof. exact (eq_refl (term133 c a b)). Qed.
Lemma lem5257314 (c : real) (a : real) (b : real) : (term134 c a b) = (term136 c a b).
Proof. exact (MK_COMB (@lem5257313 c a b) (@lem5257298 c a b)). Qed.
Lemma lem5257315 (c : real) (a : real) (b : real) : (term94 c a b) = (term136 c a b).
Proof. exact (TRANS (@lem5257281 c a b) (@lem5257314 c a b)). Qed.
Lemma lem5257317 (c : real) (a : real) (b : real) : (term137 c a b) = (term113 c a b).
Proof. exact (eq_refl (term137 c a b)). Qed.
Lemma lem5257318 (c : real) (a : real) (b : real) : (term113 c a b) = (term137 c a b).
Proof. exact (SYM (@lem5257317 c a b)). Qed.
Lemma lem5257319 (a : real) (c : real) (b : real) : (term137 c a b) = (term138 a c b).
Proof. exact (@lem1483429 a (term139 b a c) b). Qed.
Lemma lem5257320 (a : real) (c : real) (b : real) : (term113 c a b) = (term138 a c b).
Proof. exact (TRANS (@lem5257318 c a b) (@lem5257319 a c b)). Qed.
Lemma lem5257321 (a : real) (c : real) (b : real) : (term140 a c b) = (term141 a c b).
Proof. exact (eq_refl (term140 a c b)). Qed.
Lemma lem5257322 (a : real) (b : real) : (term142 a b) = (term142 a b).
Proof. exact (eq_refl (term142 a b)). Qed.
Lemma lem5257323 (a : real) (c : real) (b : real) : (term143 a c b) = (term144 a c b).
Proof. exact (MK_COMB (@lem5257322 a b) (@lem5257321 a c b)). Qed.
Lemma lem5257324 (b : real) (c : real) (a : real) : (term145 b c a) = (term146 b c a).
Proof. exact (eq_refl (term145 b c a)). Qed.
Lemma lem5257325 (b : real) (a : real) : (term147 b a) = (term147 b a).
Proof. exact (eq_refl (term147 b a)). Qed.
Lemma lem5257326 (b : real) (c : real) (a : real) : (term148 b c a) = (term149 b c a).
Proof. exact (MK_COMB (@lem5257325 b a) (@lem5257324 b c a)). Qed.
Lemma lem5257327 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5257328 (b : real) (c : real) (a : real) : (term150 b c a) = (term151 b c a).
Proof. exact (MK_COMB (@lem5257327) (@lem5257326 b c a)). Qed.
Lemma lem5257329 (a : real) (c : real) (b : real) : (term138 a c b) = (term152 a c b).
Proof. exact (MK_COMB (@lem5257328 b c a) (@lem5257323 a c b)). Qed.
Lemma lem5257330 (c : real) (a : real) (b : real) : (term153 c a b) = (term153 c a b).
Proof. exact (eq_refl (term153 c a b)). Qed.
Lemma lem5257331 (a : real) (c : real) (b : real) : ((term113 c a b) = (term138 a c b)) = ((term113 c a b) = (term152 a c b)).
Proof. exact (MK_COMB (@lem5257330 c a b) (@lem5257329 a c b)). Qed.
Lemma lem5257332 (a : real) (c : real) (b : real) : (term113 c a b) = (term152 a c b).
Proof. exact (EQ_MP (@lem5257331 a c b) (@lem5257320 a c b)). Qed.
Lemma lem5257333 (b : real) (a : real) : (real_ge b a) = (term95 b a).
Proof. exact (@lem1988291 b a). Qed.
Lemma lem5257339 (b : real) (a : real) : (real_sub b a) = (term96 b a).
Proof. exact (@lem1982792 b a). Qed.
Lemma lem5257344 (a : real) (b : real) : (term96 b a) = (term116 a b).
Proof. exact (@lem1982761 (term117 a) b). Qed.
Lemma lem5257346 (a : real) (b : real) : (real_sub b a) = (term116 a b).
Proof. exact (TRANS (@lem5257339 b a) (@lem5257344 a b)). Qed.
Lemma lem5257347 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5257348 (a : real) (b : real) : (term97 b a) = (term154 a b).
Proof. exact (MK_COMB (@lem5257347) (@lem5257346 a b)). Qed.
Lemma lem5257349 : term99 = term99.
Proof. exact (eq_refl term99). Qed.
Lemma lem5257350 (a : real) (b : real) : (term95 b a) = (term155 a b).
Proof. exact (MK_COMB (@lem5257348 a b) (@lem5257349)). Qed.
Lemma lem5257351 (a : real) (b : real) : (real_ge b a) = (term155 a b).
Proof. exact (TRANS (@lem5257333 b a) (@lem5257350 a b)). Qed.
Lemma lem5257352 (b : real) (c : real) : (term100 b c) = (term156 b c).
Proof. exact (@lem1988291 (term96 b c) term99). Qed.
Lemma lem5257370 (b : real) (c : real) : (term157 b c) = (term158 b c).
Proof. exact (@lem1982792 (term96 b c) term99). Qed.
Lemma lem5257372 (x : nat) : (real_of_num x) = (term159 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5257373 : term99 = term160.
Proof. exact (@lem5257372 (NUMERAL 0)). Qed.
Lemma lem5257375 (x : nat) : (term161 x) = (term162 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5257376 : term163 = term164.
Proof. exact (@lem5257375 term165). Qed.
Lemma lem5257377 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5257378 : term166 = term167.
Proof. exact (MK_COMB (@lem5257377) (@lem5257376)). Qed.
Lemma lem5257379 : term168 = term169.
Proof. exact (MK_COMB (@lem5257378) (@lem5257373)). Qed.
Lemma lem5257380 : term169 = term170.
Proof. exact (@lem1981613 term163 term99 term171 term171). Qed.
Lemma lem5257382 (m : nat) (n : nat) : (term172 m n) = (term173 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5257383 : term174 = term175.
Proof. exact (@lem5257382 term165 term165). Qed.
Lemma lem5257384 : (term176 = (BIT1 0)) = (term177 = term165).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5257385 : term177 = term165.
Proof. exact (EQ_MP (@lem5257384) (@lem940073)). Qed.
Lemma lem5257386 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5257387 : term175 = term171.
Proof. exact (MK_COMB (@lem5257386) (@lem5257385)). Qed.
Lemma lem5257388 : term174 = term171.
Proof. exact (TRANS (@lem5257383) (@lem5257387)). Qed.
Lemma lem5257390 (x : nat) : (term178 x) = term99.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5257391 : term168 = term99.
Proof. exact (@lem5257390 term165). Qed.
Lemma lem5257392 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5257393 : term179 = term180.
Proof. exact (MK_COMB (@lem5257392) (@lem5257391)). Qed.
Lemma lem5257394 : term170 = term160.
Proof. exact (MK_COMB (@lem5257393) (@lem5257388)). Qed.
Lemma lem5257395 : term169 = term160.
Proof. exact (TRANS (@lem5257380) (@lem5257394)). Qed.
Lemma lem5257396 : term168 = term160.
Proof. exact (TRANS (@lem5257379) (@lem5257395)). Qed.
Lemma lem5257398 (x : real) : (term181 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5257399 : term160 = term99.
Proof. exact (@lem5257398 term99). Qed.
Lemma lem5257400 : term168 = term99.
Proof. exact (TRANS (@lem5257396) (@lem5257399)). Qed.
Lemma lem5257401 (b : real) (c : real) : (term182 b c) = (term182 b c).
Proof. exact (eq_refl (term182 b c)). Qed.
Lemma lem5257402 (b : real) (c : real) : (term158 b c) = (term183 b c).
Proof. exact (MK_COMB (@lem5257401 b c) (@lem5257400)). Qed.
Lemma lem5257403 (b : real) (c : real) : (term183 b c) = (term96 b c).
Proof. exact (@lem1982723 (term96 b c)). Qed.
Lemma lem5257404 (b : real) (c : real) : (term158 b c) = (term96 b c).
Proof. exact (TRANS (@lem5257402 b c) (@lem5257403 b c)). Qed.
Lemma lem5257406 (b : real) (c : real) : (term157 b c) = (term96 b c).
Proof. exact (TRANS (@lem5257370 b c) (@lem5257404 b c)). Qed.
Lemma lem5257407 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5257408 (b : real) (c : real) : (term184 b c) = (term98 b c).
Proof. exact (MK_COMB (@lem5257407) (@lem5257406 b c)). Qed.
Lemma lem5257409 : term99 = term99.
Proof. exact (eq_refl term99). Qed.
Lemma lem5257410 (b : real) (c : real) : (term156 b c) = (term100 b c).
Proof. exact (MK_COMB (@lem5257408 b c) (@lem5257409)). Qed.
Lemma lem5257411 (b : real) (c : real) : (term100 b c) = (term100 b c).
Proof. exact (TRANS (@lem5257352 b c) (@lem5257410 b c)). Qed.
Lemma lem5257412 (a : real) (c : real) : (term100 a c) = (term156 a c).
Proof. exact (@lem1988291 (term96 a c) term99). Qed.
Lemma lem5257430 (a : real) (c : real) : (term157 a c) = (term158 a c).
Proof. exact (@lem1982792 (term96 a c) term99). Qed.
Lemma lem5257432 (x : nat) : (real_of_num x) = (term159 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5257433 : term99 = term160.
Proof. exact (@lem5257432 (NUMERAL 0)). Qed.
Lemma lem5257435 (x : nat) : (term161 x) = (term162 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5257436 : term163 = term164.
Proof. exact (@lem5257435 term165). Qed.
Lemma lem5257437 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5257438 : term166 = term167.
Proof. exact (MK_COMB (@lem5257437) (@lem5257436)). Qed.
Lemma lem5257439 : term168 = term169.
Proof. exact (MK_COMB (@lem5257438) (@lem5257433)). Qed.
Lemma lem5257440 : term169 = term170.
Proof. exact (@lem1981613 term163 term99 term171 term171). Qed.
Lemma lem5257442 (m : nat) (n : nat) : (term172 m n) = (term173 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5257443 : term174 = term175.
Proof. exact (@lem5257442 term165 term165). Qed.
Lemma lem5257444 : (term176 = (BIT1 0)) = (term177 = term165).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5257445 : term177 = term165.
Proof. exact (EQ_MP (@lem5257444) (@lem940073)). Qed.
Lemma lem5257446 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5257447 : term175 = term171.
Proof. exact (MK_COMB (@lem5257446) (@lem5257445)). Qed.
Lemma lem5257448 : term174 = term171.
Proof. exact (TRANS (@lem5257443) (@lem5257447)). Qed.
Lemma lem5257450 (x : nat) : (term178 x) = term99.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5257451 : term168 = term99.
Proof. exact (@lem5257450 term165). Qed.
Lemma lem5257452 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5257453 : term179 = term180.
Proof. exact (MK_COMB (@lem5257452) (@lem5257451)). Qed.
Lemma lem5257454 : term170 = term160.
Proof. exact (MK_COMB (@lem5257453) (@lem5257448)). Qed.
Lemma lem5257455 : term169 = term160.
Proof. exact (TRANS (@lem5257440) (@lem5257454)). Qed.
Lemma lem5257456 : term168 = term160.
Proof. exact (TRANS (@lem5257439) (@lem5257455)). Qed.
Lemma lem5257458 (x : real) : (term181 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5257459 : term160 = term99.
Proof. exact (@lem5257458 term99). Qed.
Lemma lem5257460 : term168 = term99.
Proof. exact (TRANS (@lem5257456) (@lem5257459)). Qed.
Lemma lem5257461 (a : real) (c : real) : (term182 a c) = (term182 a c).
Proof. exact (eq_refl (term182 a c)). Qed.
Lemma lem5257462 (a : real) (c : real) : (term158 a c) = (term183 a c).
Proof. exact (MK_COMB (@lem5257461 a c) (@lem5257460)). Qed.
Lemma lem5257463 (a : real) (c : real) : (term183 a c) = (term96 a c).
Proof. exact (@lem1982723 (term96 a c)). Qed.
Lemma lem5257464 (a : real) (c : real) : (term158 a c) = (term96 a c).
Proof. exact (TRANS (@lem5257462 a c) (@lem5257463 a c)). Qed.
Lemma lem5257466 (a : real) (c : real) : (term157 a c) = (term96 a c).
Proof. exact (TRANS (@lem5257430 a c) (@lem5257464 a c)). Qed.
Lemma lem5257467 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5257468 (a : real) (c : real) : (term184 a c) = (term98 a c).
Proof. exact (MK_COMB (@lem5257467) (@lem5257466 a c)). Qed.
Lemma lem5257469 : term99 = term99.
Proof. exact (eq_refl term99). Qed.
Lemma lem5257470 (a : real) (c : real) : (term156 a c) = (term100 a c).
Proof. exact (MK_COMB (@lem5257468 a c) (@lem5257469)). Qed.
Lemma lem5257471 (a : real) (c : real) : (term100 a c) = (term100 a c).
Proof. exact (TRANS (@lem5257412 a c) (@lem5257470 a c)). Qed.
Lemma lem5257472 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5257473 (b : real) (c : real) : (term101 b c) = (term101 b c).
Proof. exact (MK_COMB (@lem5257472) (@lem5257411 b c)). Qed.
Lemma lem5257474 (b : real) (a : real) (c : real) : (term102 b a c) = (term102 b a c).
Proof. exact (MK_COMB (@lem5257473 b c) (@lem5257471 a c)). Qed.
Lemma lem5257475 (c : real) (a : real) : (term185 c a) = (term186 c a).
Proof. exact (@lem1988289 (term96 c a) term99). Qed.
Lemma lem5257476 : term99 = term99.
Proof. exact (eq_refl term99). Qed.
Lemma lem5257489 (a : real) (c : real) : (term96 c a) = (term116 a c).
Proof. exact (@lem1982761 (term117 a) c). Qed.
Lemma lem5257490 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem5257491 (a : real) (c : real) : (term187 c a) = (term188 a c).
Proof. exact (MK_COMB (@lem5257490) (@lem5257489 a c)). Qed.
Lemma lem5257492 (a : real) (c : real) : (term157 c a) = (term189 a c).
Proof. exact (MK_COMB (@lem5257491 a c) (@lem5257476)). Qed.
Lemma lem5257493 (a : real) (c : real) : (term189 a c) = (term190 a c).
Proof. exact (@lem1982792 (term116 a c) term99). Qed.
Lemma lem5257495 (x : nat) : (real_of_num x) = (term159 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5257496 : term99 = term160.
Proof. exact (@lem5257495 (NUMERAL 0)). Qed.
Lemma lem5257498 (x : nat) : (term161 x) = (term162 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5257499 : term163 = term164.
Proof. exact (@lem5257498 term165). Qed.
Lemma lem5257500 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5257501 : term166 = term167.
Proof. exact (MK_COMB (@lem5257500) (@lem5257499)). Qed.
Lemma lem5257502 : term168 = term169.
Proof. exact (MK_COMB (@lem5257501) (@lem5257496)). Qed.
Lemma lem5257503 : term169 = term170.
Proof. exact (@lem1981613 term163 term99 term171 term171). Qed.
Lemma lem5257505 (m : nat) (n : nat) : (term172 m n) = (term173 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5257506 : term174 = term175.
Proof. exact (@lem5257505 term165 term165). Qed.
Lemma lem5257507 : (term176 = (BIT1 0)) = (term177 = term165).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5257508 : term177 = term165.
Proof. exact (EQ_MP (@lem5257507) (@lem940073)). Qed.
Lemma lem5257509 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5257510 : term175 = term171.
Proof. exact (MK_COMB (@lem5257509) (@lem5257508)). Qed.
Lemma lem5257511 : term174 = term171.
Proof. exact (TRANS (@lem5257506) (@lem5257510)). Qed.
Lemma lem5257513 (x : nat) : (term178 x) = term99.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5257514 : term168 = term99.
Proof. exact (@lem5257513 term165). Qed.
Lemma lem5257515 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5257516 : term179 = term180.
Proof. exact (MK_COMB (@lem5257515) (@lem5257514)). Qed.
Lemma lem5257517 : term170 = term160.
Proof. exact (MK_COMB (@lem5257516) (@lem5257511)). Qed.
Lemma lem5257518 : term169 = term160.
Proof. exact (TRANS (@lem5257503) (@lem5257517)). Qed.
Lemma lem5257519 : term168 = term160.
Proof. exact (TRANS (@lem5257502) (@lem5257518)). Qed.
Lemma lem5257521 (x : real) : (term181 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5257522 : term160 = term99.
Proof. exact (@lem5257521 term99). Qed.
Lemma lem5257523 : term168 = term99.
Proof. exact (TRANS (@lem5257519) (@lem5257522)). Qed.
Lemma lem5257524 (a : real) (c : real) : (term191 a c) = (term191 a c).
Proof. exact (eq_refl (term191 a c)). Qed.
Lemma lem5257525 (a : real) (c : real) : (term190 a c) = (term192 a c).
Proof. exact (MK_COMB (@lem5257524 a c) (@lem5257523)). Qed.
Lemma lem5257526 (a : real) (c : real) : (term192 a c) = (term116 a c).
Proof. exact (@lem1982723 (term116 a c)). Qed.
Lemma lem5257527 (a : real) (c : real) : (term190 a c) = (term116 a c).
Proof. exact (TRANS (@lem5257525 a c) (@lem5257526 a c)). Qed.
Lemma lem5257528 (a : real) (c : real) : (term189 a c) = (term116 a c).
Proof. exact (TRANS (@lem5257493 a c) (@lem5257527 a c)). Qed.
Lemma lem5257529 (a : real) (c : real) : (term157 c a) = (term116 a c).
Proof. exact (TRANS (@lem5257492 a c) (@lem5257528 a c)). Qed.
Lemma lem5257530 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5257531 (a : real) (c : real) : (term193 c a) = (term119 a c).
Proof. exact (MK_COMB (@lem5257530) (@lem5257529 a c)). Qed.
Lemma lem5257532 : term99 = term99.
Proof. exact (eq_refl term99). Qed.
Lemma lem5257533 (a : real) (c : real) : (term186 c a) = (term120 a c).
Proof. exact (MK_COMB (@lem5257531 a c) (@lem5257532)). Qed.
Lemma lem5257534 (a : real) (c : real) : (term185 c a) = (term120 a c).
Proof. exact (TRANS (@lem5257475 c a) (@lem5257533 a c)). Qed.
Lemma lem5257535 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5257536 (b : real) (a : real) (c : real) : (term111 b a c) = (term111 b a c).
Proof. exact (MK_COMB (@lem5257535) (@lem5257474 b a c)). Qed.
Lemma lem5257537 (b : real) (a : real) (c : real) : (term146 b c a) = (term194 b a c).
Proof. exact (MK_COMB (@lem5257536 b a c) (@lem5257534 a c)). Qed.
Lemma lem5257538 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5257539 (a : real) (b : real) : (term147 b a) = (term195 a b).
Proof. exact (MK_COMB (@lem5257538) (@lem5257351 a b)). Qed.
Lemma lem5257540 (b : real) (a : real) (c : real) : (term149 b c a) = (term196 b a c).
Proof. exact (MK_COMB (@lem5257539 a b) (@lem5257537 b a c)). Qed.
Lemma lem5257541 (a : real) (b : real) : (real_gt a b) = (term115 a b).
Proof. exact (@lem1988289 a b). Qed.
Lemma lem5257554 (a : real) (b : real) : (real_sub a b) = (term96 a b).
Proof. exact (@lem1982792 a b). Qed.
Lemma lem5257555 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5257556 (a : real) (b : real) : (term118 a b) = (term197 a b).
Proof. exact (MK_COMB (@lem5257555) (@lem5257554 a b)). Qed.
Lemma lem5257557 : term99 = term99.
Proof. exact (eq_refl term99). Qed.
Lemma lem5257558 (a : real) (b : real) : (term115 a b) = (term185 a b).
Proof. exact (MK_COMB (@lem5257556 a b) (@lem5257557)). Qed.
Lemma lem5257559 (a : real) (b : real) : (real_gt a b) = (term185 a b).
Proof. exact (TRANS (@lem5257541 a b) (@lem5257558 a b)). Qed.
Lemma lem5257560 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5257561 (b : real) (c : real) : (term101 b c) = (term101 b c).
Proof. exact (MK_COMB (@lem5257560) (@lem5257411 b c)). Qed.
Lemma lem5257562 (b : real) (a : real) (c : real) : (term102 b a c) = (term102 b a c).
Proof. exact (MK_COMB (@lem5257561 b c) (@lem5257471 a c)). Qed.
Lemma lem5257563 (c : real) (b : real) : (term185 c b) = (term186 c b).
Proof. exact (@lem1988289 (term96 c b) term99). Qed.
Lemma lem5257564 : term99 = term99.
Proof. exact (eq_refl term99). Qed.
Lemma lem5257577 (b : real) (c : real) : (term96 c b) = (term116 b c).
Proof. exact (@lem1982761 (term117 b) c). Qed.
Lemma lem5257578 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem5257579 (b : real) (c : real) : (term187 c b) = (term188 b c).
Proof. exact (MK_COMB (@lem5257578) (@lem5257577 b c)). Qed.
Lemma lem5257580 (b : real) (c : real) : (term157 c b) = (term189 b c).
Proof. exact (MK_COMB (@lem5257579 b c) (@lem5257564)). Qed.
Lemma lem5257581 (b : real) (c : real) : (term189 b c) = (term190 b c).
Proof. exact (@lem1982792 (term116 b c) term99). Qed.
Lemma lem5257583 (x : nat) : (real_of_num x) = (term159 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5257584 : term99 = term160.
Proof. exact (@lem5257583 (NUMERAL 0)). Qed.
Lemma lem5257586 (x : nat) : (term161 x) = (term162 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5257587 : term163 = term164.
Proof. exact (@lem5257586 term165). Qed.
Lemma lem5257588 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5257589 : term166 = term167.
Proof. exact (MK_COMB (@lem5257588) (@lem5257587)). Qed.
Lemma lem5257590 : term168 = term169.
Proof. exact (MK_COMB (@lem5257589) (@lem5257584)). Qed.
Lemma lem5257591 : term169 = term170.
Proof. exact (@lem1981613 term163 term99 term171 term171). Qed.
Lemma lem5257593 (m : nat) (n : nat) : (term172 m n) = (term173 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5257594 : term174 = term175.
Proof. exact (@lem5257593 term165 term165). Qed.
Lemma lem5257595 : (term176 = (BIT1 0)) = (term177 = term165).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5257596 : term177 = term165.
Proof. exact (EQ_MP (@lem5257595) (@lem940073)). Qed.
Lemma lem5257597 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5257598 : term175 = term171.
Proof. exact (MK_COMB (@lem5257597) (@lem5257596)). Qed.
Lemma lem5257599 : term174 = term171.
Proof. exact (TRANS (@lem5257594) (@lem5257598)). Qed.
Lemma lem5257601 (x : nat) : (term178 x) = term99.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5257602 : term168 = term99.
Proof. exact (@lem5257601 term165). Qed.
Lemma lem5257603 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5257604 : term179 = term180.
Proof. exact (MK_COMB (@lem5257603) (@lem5257602)). Qed.
Lemma lem5257605 : term170 = term160.
Proof. exact (MK_COMB (@lem5257604) (@lem5257599)). Qed.
Lemma lem5257606 : term169 = term160.
Proof. exact (TRANS (@lem5257591) (@lem5257605)). Qed.
Lemma lem5257607 : term168 = term160.
Proof. exact (TRANS (@lem5257590) (@lem5257606)). Qed.
Lemma lem5257609 (x : real) : (term181 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5257610 : term160 = term99.
Proof. exact (@lem5257609 term99). Qed.
Lemma lem5257611 : term168 = term99.
Proof. exact (TRANS (@lem5257607) (@lem5257610)). Qed.
Lemma lem5257612 (b : real) (c : real) : (term191 b c) = (term191 b c).
Proof. exact (eq_refl (term191 b c)). Qed.
Lemma lem5257613 (b : real) (c : real) : (term190 b c) = (term192 b c).
Proof. exact (MK_COMB (@lem5257612 b c) (@lem5257611)). Qed.
Lemma lem5257614 (b : real) (c : real) : (term192 b c) = (term116 b c).
Proof. exact (@lem1982723 (term116 b c)). Qed.
Lemma lem5257615 (b : real) (c : real) : (term190 b c) = (term116 b c).
Proof. exact (TRANS (@lem5257613 b c) (@lem5257614 b c)). Qed.
Lemma lem5257616 (b : real) (c : real) : (term189 b c) = (term116 b c).
Proof. exact (TRANS (@lem5257581 b c) (@lem5257615 b c)). Qed.
Lemma lem5257617 (b : real) (c : real) : (term157 c b) = (term116 b c).
Proof. exact (TRANS (@lem5257580 b c) (@lem5257616 b c)). Qed.
Lemma lem5257618 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5257619 (b : real) (c : real) : (term193 c b) = (term119 b c).
Proof. exact (MK_COMB (@lem5257618) (@lem5257617 b c)). Qed.
Lemma lem5257620 : term99 = term99.
Proof. exact (eq_refl term99). Qed.
Lemma lem5257621 (b : real) (c : real) : (term186 c b) = (term120 b c).
Proof. exact (MK_COMB (@lem5257619 b c) (@lem5257620)). Qed.
Lemma lem5257622 (b : real) (c : real) : (term185 c b) = (term120 b c).
Proof. exact (TRANS (@lem5257563 c b) (@lem5257621 b c)). Qed.
Lemma lem5257623 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5257624 (b : real) (a : real) (c : real) : (term111 b a c) = (term111 b a c).
Proof. exact (MK_COMB (@lem5257623) (@lem5257562 b a c)). Qed.
Lemma lem5257625 (a : real) (b : real) (c : real) : (term141 a c b) = (term198 a b c).
Proof. exact (MK_COMB (@lem5257624 b a c) (@lem5257622 b c)). Qed.
Lemma lem5257626 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5257627 (a : real) (b : real) : (term142 a b) = (term199 a b).
Proof. exact (MK_COMB (@lem5257626) (@lem5257559 a b)). Qed.
Lemma lem5257628 (a : real) (b : real) (c : real) : (term144 a c b) = (term200 a b c).
Proof. exact (MK_COMB (@lem5257627 a b) (@lem5257625 a b c)). Qed.
Lemma lem5257629 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5257630 (b : real) (a : real) (c : real) : (term151 b c a) = (term201 b a c).
Proof. exact (MK_COMB (@lem5257629) (@lem5257540 b a c)). Qed.
Lemma lem5257631 (a : real) (b : real) (c : real) : (term152 a c b) = (term202 a b c).
Proof. exact (MK_COMB (@lem5257630 b a c) (@lem5257628 a b c)). Qed.
Lemma lem5257643 (a : real) (b : real) (c : real) : (term113 c a b) = (term202 a b c).
Proof. exact (TRANS (@lem5257332 a c b) (@lem5257631 a b c)). Qed.
Lemma lem5257645 (x : real) (a : real) (y : real) (r : real) : (term203 a x y r) = (term204 x a y r).
Proof. exact (proj1 (@lem1482698 x a (@el real) y (@el real) r)). Qed.
Lemma lem5257646 (a : real) (c : real) (b : real) : (term130 c a b) = (term205 a c b).
Proof. exact (@lem5257645 a (term117 c) b term99). Qed.
Lemma lem5257659 (b : real) (c : real) : (term116 c b) = (term96 b c).
Proof. exact (@lem1982761 b (term117 c)). Qed.
Lemma lem5257660 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5257661 (b : real) (c : real) : (term154 c b) = (term98 b c).
Proof. exact (MK_COMB (@lem5257660) (@lem5257659 b c)). Qed.
Lemma lem5257662 : term99 = term99.
Proof. exact (eq_refl term99). Qed.
Lemma lem5257663 (b : real) (c : real) : (term155 c b) = (term100 b c).
Proof. exact (MK_COMB (@lem5257661 b c) (@lem5257662)). Qed.
Lemma lem5257676 (a : real) (c : real) : (term116 c a) = (term96 a c).
Proof. exact (@lem1982761 a (term117 c)). Qed.
Lemma lem5257677 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5257678 (a : real) (c : real) : (term154 c a) = (term98 a c).
Proof. exact (MK_COMB (@lem5257677) (@lem5257676 a c)). Qed.
Lemma lem5257679 : term99 = term99.
Proof. exact (eq_refl term99). Qed.
Lemma lem5257680 (a : real) (c : real) : (term155 c a) = (term100 a c).
Proof. exact (MK_COMB (@lem5257678 a c) (@lem5257679)). Qed.
Lemma lem5257681 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5257682 (a : real) (c : real) : (term195 c a) = (term101 a c).
Proof. exact (MK_COMB (@lem5257681) (@lem5257680 a c)). Qed.
Lemma lem5257683 (a : real) (b : real) (c : real) : (term205 a c b) = (term102 a b c).
Proof. exact (MK_COMB (@lem5257682 a c) (@lem5257663 b c)). Qed.
Lemma lem5257684 (a : real) (b : real) (c : real) : (term130 c a b) = (term102 a b c).
Proof. exact (TRANS (@lem5257646 a c b) (@lem5257683 a b c)). Qed.
Lemma lem5257685 (b : real) (c : real) : (term206 b c) = (term206 b c).
Proof. exact (eq_refl (term206 b c)). Qed.
Lemma lem5257688 (a : real) (b : real) (c : real) : (term207 c a b) = (term208 a b c).
Proof. exact (MK_COMB (@lem5257685 b c) (@lem5257684 a b c)). Qed.
Lemma lem5257690 (x : real) (a : real) (y : real) (r : real) : (term203 a x y r) = (term204 x a y r).
Proof. exact (proj1 (@lem1482698 x a (@el real) y (@el real) r)). Qed.
Lemma lem5257691 (a : real) (c : real) (b : real) : (term130 c a b) = (term205 a c b).
Proof. exact (@lem5257690 a (term117 c) b term99). Qed.
Lemma lem5257704 (b : real) (c : real) : (term116 c b) = (term96 b c).
Proof. exact (@lem1982761 b (term117 c)). Qed.
Lemma lem5257705 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5257706 (b : real) (c : real) : (term154 c b) = (term98 b c).
Proof. exact (MK_COMB (@lem5257705) (@lem5257704 b c)). Qed.
Lemma lem5257707 : term99 = term99.
Proof. exact (eq_refl term99). Qed.
Lemma lem5257708 (b : real) (c : real) : (term155 c b) = (term100 b c).
Proof. exact (MK_COMB (@lem5257706 b c) (@lem5257707)). Qed.
Lemma lem5257721 (a : real) (c : real) : (term116 c a) = (term96 a c).
Proof. exact (@lem1982761 a (term117 c)). Qed.
Lemma lem5257722 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5257723 (a : real) (c : real) : (term154 c a) = (term98 a c).
Proof. exact (MK_COMB (@lem5257722) (@lem5257721 a c)). Qed.
Lemma lem5257724 : term99 = term99.
Proof. exact (eq_refl term99). Qed.
Lemma lem5257725 (a : real) (c : real) : (term155 c a) = (term100 a c).
Proof. exact (MK_COMB (@lem5257723 a c) (@lem5257724)). Qed.
Lemma lem5257726 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5257727 (a : real) (c : real) : (term195 c a) = (term101 a c).
Proof. exact (MK_COMB (@lem5257726) (@lem5257725 a c)). Qed.
Lemma lem5257728 (a : real) (b : real) (c : real) : (term205 a c b) = (term102 a b c).
Proof. exact (MK_COMB (@lem5257727 a c) (@lem5257708 b c)). Qed.
Lemma lem5257729 (a : real) (b : real) (c : real) : (term130 c a b) = (term102 a b c).
Proof. exact (TRANS (@lem5257691 a c b) (@lem5257728 a b c)). Qed.
Lemma lem5257730 (a : real) (c : real) : (term206 a c) = (term206 a c).
Proof. exact (eq_refl (term206 a c)). Qed.
Lemma lem5257733 (a : real) (b : real) (c : real) : (term209 c a b) = (term210 a b c).
Proof. exact (MK_COMB (@lem5257730 a c) (@lem5257729 a b c)). Qed.
Lemma lem5257734 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5257735 (a : real) (b : real) (c : real) : (term211 c a b) = (term212 a b c).
Proof. exact (MK_COMB (@lem5257734) (@lem5257688 a b c)). Qed.
Lemma lem5257736 (a : real) (b : real) (c : real) : (term135 c a b) = (term213 a b c).
Proof. exact (MK_COMB (@lem5257735 a b c) (@lem5257733 a b c)). Qed.
Lemma lem5257737 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5257738 (a : real) (b : real) (c : real) : (term133 c a b) = (term214 a b c).
Proof. exact (MK_COMB (@lem5257737) (@lem5257643 a b c)). Qed.
Lemma lem5257739 (a : real) (b : real) (c : real) : (term136 c a b) = (term215 a b c).
Proof. exact (MK_COMB (@lem5257738 a b c) (@lem5257736 a b c)). Qed.
Lemma lem5257740 (a : real) (b : real) (c : real) (h1 : term215 a b c) : term215 a b c.
Proof. exact (h1). Qed.
Lemma lem5257741 (a : real) (b : real) (c : real) (h1 : term202 a b c) : term202 a b c.
Proof. exact (h1). Qed.
Lemma lem5257742 (b : real) (a : real) (c : real) (h1 : term196 b a c) : term196 b a c.
Proof. exact (h1). Qed.
Lemma lem5257743 (b : real) (a : real) (c : real) (h1 : term196 b a c) : term194 b a c.
Proof. exact (proj2 (@lem5257742 b a c h1)). Qed.
Lemma lem5257745 (b : real) (a : real) (c : real) (h1 : term196 b a c) : term120 a c.
Proof. exact (proj2 (@lem5257743 b a c h1)). Qed.
Lemma lem5257746 (b : real) (a : real) (c : real) (h1 : term196 b a c) : term102 b a c.
Proof. exact (proj1 (@lem5257743 b a c h1)). Qed.
Lemma lem5257747 (b : real) (a : real) (c : real) (h1 : term196 b a c) : term100 a c.
Proof. exact (proj2 (@lem5257746 b a c h1)). Qed.
Lemma lem5257750 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5257751 : term216 = term217.
Proof. exact (@lem5257750 term99 term171). Qed.
Lemma lem5257753 (x : nat) : (real_of_num x) = (term159 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5257754 : term171 = term218.
Proof. exact (@lem5257753 term165). Qed.
Lemma lem5257756 (x : nat) : (real_of_num x) = (term159 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5257757 : term99 = term160.
Proof. exact (@lem5257756 (NUMERAL 0)). Qed.
Lemma lem5257758 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5257759 : term219 = term220.
Proof. exact (MK_COMB (@lem5257758) (@lem5257757)). Qed.
Lemma lem5257760 : term217 = term221.
Proof. exact (MK_COMB (@lem5257759) (@lem5257754)). Qed.
Lemma lem5257761 : term222.
Proof. exact (@lem1980255 term99 term171 term171 term171). Qed.
Lemma lem5257763 (m : nat) (n : nat) : (term223 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5257764 : term217 = term224.
Proof. exact (@lem5257763 (NUMERAL 0) term165). Qed.
Lemma lem5257765 : term225 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5257766 (h1 : term225 = (BIT1 0)) : term224 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5257767 : (term225 = (BIT1 0)) = (term224 = True).
Proof. exact (prop_ext (fun h1 : term225 = (BIT1 0) => @lem5257766 h1) (fun h1 : term224 = True => @lem5257765)). Qed.
Lemma lem5257768 : term224 = True.
Proof. exact (EQ_MP (@lem5257767) (@lem5257765)). Qed.
Lemma lem5257769 : term217 = True.
Proof. exact (TRANS (@lem5257764) (@lem5257768)). Qed.
Lemma lem5257770 : True = term217.
Proof. exact (SYM (@lem5257769)). Qed.
Lemma lem5257771 : term217.
Proof. exact (EQ_MP (@lem5257770) (@lem0)). Qed.
Lemma lem5257772 : term226.
Proof. exact (@lem5257761 (@lem5257771)). Qed.
Lemma lem5257774 (m : nat) (n : nat) : (term223 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5257775 : term217 = term224.
Proof. exact (@lem5257774 (NUMERAL 0) term165). Qed.
Lemma lem5257776 : term225 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5257777 (h1 : term225 = (BIT1 0)) : term224 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5257778 : (term225 = (BIT1 0)) = (term224 = True).
Proof. exact (prop_ext (fun h1 : term225 = (BIT1 0) => @lem5257777 h1) (fun h1 : term224 = True => @lem5257776)). Qed.
Lemma lem5257779 : term224 = True.
Proof. exact (EQ_MP (@lem5257778) (@lem5257776)). Qed.
Lemma lem5257780 : term217 = True.
Proof. exact (TRANS (@lem5257775) (@lem5257779)). Qed.
Lemma lem5257781 : True = term217.
Proof. exact (SYM (@lem5257780)). Qed.
Lemma lem5257782 : term217.
Proof. exact (EQ_MP (@lem5257781) (@lem0)). Qed.
Lemma lem5257783 : term221 = term227.
Proof. exact (@lem5257772 (@lem5257782)). Qed.
Lemma lem5257785 (m : nat) (n : nat) : (term172 m n) = (term173 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5257786 : term174 = term175.
Proof. exact (@lem5257785 term165 term165). Qed.
Lemma lem5257787 : (term176 = (BIT1 0)) = (term177 = term165).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5257788 : term177 = term165.
Proof. exact (EQ_MP (@lem5257787) (@lem940073)). Qed.
Lemma lem5257789 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5257790 : term175 = term171.
Proof. exact (MK_COMB (@lem5257789) (@lem5257788)). Qed.
Lemma lem5257791 : term174 = term171.
Proof. exact (TRANS (@lem5257786) (@lem5257790)). Qed.
Lemma lem5257793 (x : nat) : (term228 x) = term99.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5257794 : term229 = term99.
Proof. exact (@lem5257793 term165). Qed.
Lemma lem5257795 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5257796 : term230 = term219.
Proof. exact (MK_COMB (@lem5257795) (@lem5257794)). Qed.
Lemma lem5257797 : term227 = term217.
Proof. exact (MK_COMB (@lem5257796) (@lem5257791)). Qed.
Lemma lem5257799 (m : nat) (n : nat) : (term223 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5257800 : term217 = term224.
Proof. exact (@lem5257799 (NUMERAL 0) term165). Qed.
Lemma lem5257801 : term225 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5257802 (h1 : term225 = (BIT1 0)) : term224 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5257803 : (term225 = (BIT1 0)) = (term224 = True).
Proof. exact (prop_ext (fun h1 : term225 = (BIT1 0) => @lem5257802 h1) (fun h1 : term224 = True => @lem5257801)). Qed.
Lemma lem5257804 : term224 = True.
Proof. exact (EQ_MP (@lem5257803) (@lem5257801)). Qed.
Lemma lem5257805 : term217 = True.
Proof. exact (TRANS (@lem5257800) (@lem5257804)). Qed.
Lemma lem5257806 : term227 = True.
Proof. exact (TRANS (@lem5257797) (@lem5257805)). Qed.
Lemma lem5257807 : term221 = True.
Proof. exact (TRANS (@lem5257783) (@lem5257806)). Qed.
Lemma lem5257808 : term217 = True.
Proof. exact (TRANS (@lem5257760) (@lem5257807)). Qed.
Lemma lem5257809 : term216 = True.
Proof. exact (TRANS (@lem5257751) (@lem5257808)). Qed.
Lemma lem5257810 : True = term216.
Proof. exact (SYM (@lem5257809)). Qed.
Lemma lem5257811 : term216.
Proof. exact (EQ_MP (@lem5257810) (@lem0)). Qed.
Lemma lem5257812 (b : real) (a : real) (c : real) (h1 : term196 b a c) : term231 a c.
Proof. exact (conj (@lem5257811) (@lem5257747 b a c h1)). Qed.
Lemma lem5257814 (x : real) (y : real) : term232 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5257815 (a : real) (c : real) : term233 a c.
Proof. exact (@lem5257814 term171 (term96 a c)). Qed.
Lemma lem5257816 (b : real) (a : real) (c : real) (h1 : term196 b a c) : term234 a c.
Proof. exact (@lem5257815 a c (@lem5257812 b a c h1)). Qed.
Lemma lem5257817 (a : real) (c : real) : (term235 a c) = (term96 a c).
Proof. exact (@lem1982733 (term96 a c)). Qed.
Lemma lem5257818 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5257819 (a : real) (c : real) : (term236 a c) = (term98 a c).
Proof. exact (MK_COMB (@lem5257818) (@lem5257817 a c)). Qed.
Lemma lem5257820 : term99 = term99.
Proof. exact (eq_refl term99). Qed.
Lemma lem5257821 (a : real) (c : real) : (term234 a c) = (term100 a c).
Proof. exact (MK_COMB (@lem5257819 a c) (@lem5257820)). Qed.
Lemma lem5257822 (b : real) (a : real) (c : real) (h1 : term196 b a c) : term100 a c.
Proof. exact (EQ_MP (@lem5257821 a c) (@lem5257816 b a c h1)). Qed.
Lemma lem5257824 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5257825 : term216 = term217.
Proof. exact (@lem5257824 term99 term171). Qed.
Lemma lem5257827 (x : nat) : (real_of_num x) = (term159 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5257828 : term171 = term218.
Proof. exact (@lem5257827 term165). Qed.
Lemma lem5257830 (x : nat) : (real_of_num x) = (term159 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5257831 : term99 = term160.
Proof. exact (@lem5257830 (NUMERAL 0)). Qed.
Lemma lem5257832 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5257833 : term219 = term220.
Proof. exact (MK_COMB (@lem5257832) (@lem5257831)). Qed.
Lemma lem5257834 : term217 = term221.
Proof. exact (MK_COMB (@lem5257833) (@lem5257828)). Qed.
Lemma lem5257835 : term222.
Proof. exact (@lem1980255 term99 term171 term171 term171). Qed.
Lemma lem5257837 (m : nat) (n : nat) : (term223 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5257838 : term217 = term224.
Proof. exact (@lem5257837 (NUMERAL 0) term165). Qed.
Lemma lem5257839 : term225 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5257840 (h1 : term225 = (BIT1 0)) : term224 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5257841 : (term225 = (BIT1 0)) = (term224 = True).
Proof. exact (prop_ext (fun h1 : term225 = (BIT1 0) => @lem5257840 h1) (fun h1 : term224 = True => @lem5257839)). Qed.
Lemma lem5257842 : term224 = True.
Proof. exact (EQ_MP (@lem5257841) (@lem5257839)). Qed.
Lemma lem5257843 : term217 = True.
Proof. exact (TRANS (@lem5257838) (@lem5257842)). Qed.
Lemma lem5257844 : True = term217.
Proof. exact (SYM (@lem5257843)). Qed.
Lemma lem5257845 : term217.
Proof. exact (EQ_MP (@lem5257844) (@lem0)). Qed.
Lemma lem5257846 : term226.
Proof. exact (@lem5257835 (@lem5257845)). Qed.
Lemma lem5257848 (m : nat) (n : nat) : (term223 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5257849 : term217 = term224.
Proof. exact (@lem5257848 (NUMERAL 0) term165). Qed.
Lemma lem5257850 : term225 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5257851 (h1 : term225 = (BIT1 0)) : term224 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5257852 : (term225 = (BIT1 0)) = (term224 = True).
Proof. exact (prop_ext (fun h1 : term225 = (BIT1 0) => @lem5257851 h1) (fun h1 : term224 = True => @lem5257850)). Qed.
Lemma lem5257853 : term224 = True.
Proof. exact (EQ_MP (@lem5257852) (@lem5257850)). Qed.
Lemma lem5257854 : term217 = True.
Proof. exact (TRANS (@lem5257849) (@lem5257853)). Qed.
Lemma lem5257855 : True = term217.
Proof. exact (SYM (@lem5257854)). Qed.
Lemma lem5257856 : term217.
Proof. exact (EQ_MP (@lem5257855) (@lem0)). Qed.
Lemma lem5257857 : term221 = term227.
Proof. exact (@lem5257846 (@lem5257856)). Qed.
Lemma lem5257859 (m : nat) (n : nat) : (term172 m n) = (term173 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5257860 : term174 = term175.
Proof. exact (@lem5257859 term165 term165). Qed.
Lemma lem5257861 : (term176 = (BIT1 0)) = (term177 = term165).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5257862 : term177 = term165.
Proof. exact (EQ_MP (@lem5257861) (@lem940073)). Qed.
Lemma lem5257863 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5257864 : term175 = term171.
Proof. exact (MK_COMB (@lem5257863) (@lem5257862)). Qed.
Lemma lem5257865 : term174 = term171.
Proof. exact (TRANS (@lem5257860) (@lem5257864)). Qed.
Lemma lem5257867 (x : nat) : (term228 x) = term99.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5257868 : term229 = term99.
Proof. exact (@lem5257867 term165). Qed.
Lemma lem5257869 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5257870 : term230 = term219.
Proof. exact (MK_COMB (@lem5257869) (@lem5257868)). Qed.
Lemma lem5257871 : term227 = term217.
Proof. exact (MK_COMB (@lem5257870) (@lem5257865)). Qed.
Lemma lem5257873 (m : nat) (n : nat) : (term223 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5257874 : term217 = term224.
Proof. exact (@lem5257873 (NUMERAL 0) term165). Qed.
Lemma lem5257875 : term225 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5257876 (h1 : term225 = (BIT1 0)) : term224 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5257877 : (term225 = (BIT1 0)) = (term224 = True).
Proof. exact (prop_ext (fun h1 : term225 = (BIT1 0) => @lem5257876 h1) (fun h1 : term224 = True => @lem5257875)). Qed.
Lemma lem5257878 : term224 = True.
Proof. exact (EQ_MP (@lem5257877) (@lem5257875)). Qed.
Lemma lem5257879 : term217 = True.
Proof. exact (TRANS (@lem5257874) (@lem5257878)). Qed.
Lemma lem5257880 : term227 = True.
Proof. exact (TRANS (@lem5257871) (@lem5257879)). Qed.
Lemma lem5257881 : term221 = True.
Proof. exact (TRANS (@lem5257857) (@lem5257880)). Qed.
Lemma lem5257882 : term217 = True.
Proof. exact (TRANS (@lem5257834) (@lem5257881)). Qed.
Lemma lem5257883 : term216 = True.
Proof. exact (TRANS (@lem5257825) (@lem5257882)). Qed.
Lemma lem5257884 : True = term216.
Proof. exact (SYM (@lem5257883)). Qed.
Lemma lem5257885 : term216.
Proof. exact (EQ_MP (@lem5257884) (@lem0)). Qed.
Lemma lem5257886 (b : real) (a : real) (c : real) (h1 : term196 b a c) : term237 a c.
Proof. exact (conj (@lem5257885) (@lem5257745 b a c h1)). Qed.
Lemma lem5257888 (x : real) (y : real) : term238 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem5257889 (a : real) (c : real) : term239 a c.
Proof. exact (@lem5257888 term171 (term116 a c)). Qed.
Lemma lem5257890 (b : real) (a : real) (c : real) (h1 : term196 b a c) : term240 a c.
Proof. exact (@lem5257889 a c (@lem5257886 b a c h1)). Qed.
Lemma lem5257891 (a : real) (c : real) : (term241 a c) = (term116 a c).
Proof. exact (@lem1982733 (term116 a c)). Qed.
Lemma lem5257892 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5257893 (a : real) (c : real) : (term242 a c) = (term119 a c).
Proof. exact (MK_COMB (@lem5257892) (@lem5257891 a c)). Qed.
Lemma lem5257894 : term99 = term99.
Proof. exact (eq_refl term99). Qed.
Lemma lem5257895 (a : real) (c : real) : (term240 a c) = (term120 a c).
Proof. exact (MK_COMB (@lem5257893 a c) (@lem5257894)). Qed.
Lemma lem5257896 (b : real) (a : real) (c : real) (h1 : term196 b a c) : term120 a c.
Proof. exact (EQ_MP (@lem5257895 a c) (@lem5257890 b a c h1)). Qed.
Lemma lem5257897 (b : real) (a : real) (c : real) (h1 : term196 b a c) : term243 a c.
Proof. exact (conj (@lem5257896 b a c h1) (@lem5257822 b a c h1)). Qed.
Lemma lem5257899 (x : real) (y : real) : term244 x y.
Proof. exact (proj1 (@lem1988348 x y)). Qed.
Lemma lem5257900 (a : real) (c : real) : term245 a c.
Proof. exact (@lem5257899 (term116 a c) (term96 a c)). Qed.
Lemma lem5257901 (b : real) (a : real) (c : real) (h1 : term196 b a c) : term246 a c.
Proof. exact (@lem5257900 a c (@lem5257897 b a c h1)). Qed.
Lemma lem5257902 (a : real) (c : real) : (term247 a c) = (term248 a c).
Proof. exact (@lem1982753 (term117 a) a c (term117 c)). Qed.
Lemma lem5257903 (a : real) : (term249 a) = (term250 a).
Proof. exact (@lem1982713 term163 a). Qed.
Lemma lem5257905 (x : nat) : (real_of_num x) = (term159 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5257906 : term171 = term218.
Proof. exact (@lem5257905 term165). Qed.
Lemma lem5257908 (x : nat) : (term161 x) = (term162 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5257909 : term163 = term164.
Proof. exact (@lem5257908 term165). Qed.
Lemma lem5257910 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5257911 : term251 = term252.
Proof. exact (MK_COMB (@lem5257910) (@lem5257909)). Qed.
Lemma lem5257912 : term253 = term254.
Proof. exact (MK_COMB (@lem5257911) (@lem5257906)). Qed.
Lemma lem5257913 : term255.
Proof. exact (@lem1981473 term163 term171 term171 term171 term99 term171). Qed.
Lemma lem5257915 (m : nat) (n : nat) : (term223 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5257916 : term217 = term224.
Proof. exact (@lem5257915 (NUMERAL 0) term165). Qed.
Lemma lem5257917 : term225 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5257918 (h1 : term225 = (BIT1 0)) : term224 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5257919 : (term225 = (BIT1 0)) = (term224 = True).
Proof. exact (prop_ext (fun h1 : term225 = (BIT1 0) => @lem5257918 h1) (fun h1 : term224 = True => @lem5257917)). Qed.
Lemma lem5257920 : term224 = True.
Proof. exact (EQ_MP (@lem5257919) (@lem5257917)). Qed.
Lemma lem5257921 : term217 = True.
Proof. exact (TRANS (@lem5257916) (@lem5257920)). Qed.
Lemma lem5257922 : True = term217.
Proof. exact (SYM (@lem5257921)). Qed.
Lemma lem5257923 : term217.
Proof. exact (EQ_MP (@lem5257922) (@lem0)). Qed.
Lemma lem5257924 : term256.
Proof. exact (@lem5257913 (@lem5257923)). Qed.
Lemma lem5257926 (m : nat) (n : nat) : (term223 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5257927 : term217 = term224.
Proof. exact (@lem5257926 (NUMERAL 0) term165). Qed.
Lemma lem5257928 : term225 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5257929 (h1 : term225 = (BIT1 0)) : term224 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5257930 : (term225 = (BIT1 0)) = (term224 = True).
Proof. exact (prop_ext (fun h1 : term225 = (BIT1 0) => @lem5257929 h1) (fun h1 : term224 = True => @lem5257928)). Qed.
Lemma lem5257931 : term224 = True.
Proof. exact (EQ_MP (@lem5257930) (@lem5257928)). Qed.
Lemma lem5257932 : term217 = True.
Proof. exact (TRANS (@lem5257927) (@lem5257931)). Qed.
Lemma lem5257933 : True = term217.
Proof. exact (SYM (@lem5257932)). Qed.
Lemma lem5257934 : term217.
Proof. exact (EQ_MP (@lem5257933) (@lem0)). Qed.
Lemma lem5257935 : term257.
Proof. exact (@lem5257924 (@lem5257934)). Qed.
Lemma lem5257937 (m : nat) (n : nat) : (term223 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5257938 : term217 = term224.
Proof. exact (@lem5257937 (NUMERAL 0) term165). Qed.
Lemma lem5257939 : term225 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5257940 (h1 : term225 = (BIT1 0)) : term224 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5257941 : (term225 = (BIT1 0)) = (term224 = True).
Proof. exact (prop_ext (fun h1 : term225 = (BIT1 0) => @lem5257940 h1) (fun h1 : term224 = True => @lem5257939)). Qed.
Lemma lem5257942 : term224 = True.
Proof. exact (EQ_MP (@lem5257941) (@lem5257939)). Qed.
Lemma lem5257943 : term217 = True.
Proof. exact (TRANS (@lem5257938) (@lem5257942)). Qed.
Lemma lem5257944 : True = term217.
Proof. exact (SYM (@lem5257943)). Qed.
Lemma lem5257945 : term217.
Proof. exact (EQ_MP (@lem5257944) (@lem0)). Qed.
Lemma lem5257946 : term258.
Proof. exact (@lem5257935 (@lem5257945)). Qed.
Lemma lem5257948 (m : nat) (n : nat) : (term172 m n) = (term173 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5257949 : term174 = term175.
Proof. exact (@lem5257948 term165 term165). Qed.
Lemma lem5257950 : (term176 = (BIT1 0)) = (term177 = term165).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5257951 : term177 = term165.
Proof. exact (EQ_MP (@lem5257950) (@lem940073)). Qed.
Lemma lem5257952 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5257953 : term175 = term171.
Proof. exact (MK_COMB (@lem5257952) (@lem5257951)). Qed.
Lemma lem5257954 : term174 = term171.
Proof. exact (TRANS (@lem5257949) (@lem5257953)). Qed.
Lemma lem5257956 (m : nat) (n : nat) : (term259 m n) = (term260 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5257957 : term261 = term262.
Proof. exact (@lem5257956 term165 term165). Qed.
Lemma lem5257958 : (term176 = (BIT1 0)) = (term177 = term165).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5257959 : term177 = term165.
Proof. exact (EQ_MP (@lem5257958) (@lem940073)). Qed.
Lemma lem5257960 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5257961 : term175 = term171.
Proof. exact (MK_COMB (@lem5257960) (@lem5257959)). Qed.
Lemma lem5257962 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5257963 : term262 = term163.
Proof. exact (MK_COMB (@lem5257962) (@lem5257961)). Qed.
Lemma lem5257964 : term261 = term163.
Proof. exact (TRANS (@lem5257957) (@lem5257963)). Qed.
Lemma lem5257965 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5257966 : term263 = term251.
Proof. exact (MK_COMB (@lem5257965) (@lem5257964)). Qed.
Lemma lem5257967 : term264 = term253.
Proof. exact (MK_COMB (@lem5257966) (@lem5257954)). Qed.
Lemma lem5257969 (m : nat) : (term265 m) = term99.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5257970 : term253 = term99.
Proof. exact (@lem5257969 term165). Qed.
Lemma lem5257971 : term264 = term99.
Proof. exact (TRANS (@lem5257967) (@lem5257970)). Qed.
Lemma lem5257972 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5257973 : term266 = term267.
Proof. exact (MK_COMB (@lem5257972) (@lem5257971)). Qed.
Lemma lem5257974 : term171 = term171.
Proof. exact (eq_refl term171). Qed.
Lemma lem5257975 : term268 = term229.
Proof. exact (MK_COMB (@lem5257973) (@lem5257974)). Qed.
Lemma lem5257977 (x : nat) : (term228 x) = term99.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5257978 : term229 = term99.
Proof. exact (@lem5257977 term165). Qed.
Lemma lem5257979 : term268 = term99.
Proof. exact (TRANS (@lem5257975) (@lem5257978)). Qed.
Lemma lem5257981 (m : nat) (n : nat) : (term172 m n) = (term173 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5257982 : term174 = term175.
Proof. exact (@lem5257981 term165 term165). Qed.
Lemma lem5257983 : (term176 = (BIT1 0)) = (term177 = term165).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5257984 : term177 = term165.
Proof. exact (EQ_MP (@lem5257983) (@lem940073)). Qed.
Lemma lem5257985 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5257986 : term175 = term171.
Proof. exact (MK_COMB (@lem5257985) (@lem5257984)). Qed.
Lemma lem5257987 : term174 = term171.
Proof. exact (TRANS (@lem5257982) (@lem5257986)). Qed.
Lemma lem5257988 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem5257989 : term269 = term229.
Proof. exact (MK_COMB (@lem5257988) (@lem5257987)). Qed.
Lemma lem5257991 (x : nat) : (term228 x) = term99.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5257992 : term229 = term99.
Proof. exact (@lem5257991 term165). Qed.
Lemma lem5257993 : term269 = term99.
Proof. exact (TRANS (@lem5257989) (@lem5257992)). Qed.
Lemma lem5257994 : term99 = term269.
Proof. exact (SYM (@lem5257993)). Qed.
Lemma lem5257995 : term268 = term269.
Proof. exact (TRANS (@lem5257979) (@lem5257994)). Qed.
Lemma lem5257996 : term254 = term160.
Proof. exact (@lem5257946 (@lem5257995)). Qed.
Lemma lem5257997 : term253 = term160.
Proof. exact (TRANS (@lem5257912) (@lem5257996)). Qed.
Lemma lem5257999 (x : real) : (term181 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5258000 : term160 = term99.
Proof. exact (@lem5257999 term99). Qed.
Lemma lem5258001 : term253 = term99.
Proof. exact (TRANS (@lem5257997) (@lem5258000)). Qed.
Lemma lem5258002 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5258003 : term270 = term267.
Proof. exact (MK_COMB (@lem5258002) (@lem5258001)). Qed.
Lemma lem5258004 (a : real) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem5258005 (a : real) : (term250 a) = (term271 a).
Proof. exact (MK_COMB (@lem5258003) (@lem5258004 a)). Qed.
Lemma lem5258006 (a : real) : (term249 a) = (term271 a).
Proof. exact (TRANS (@lem5257903 a) (@lem5258005 a)). Qed.
Lemma lem5258007 (a : real) : (term271 a) = term99.
Proof. exact (@lem1982719 a). Qed.
Lemma lem5258008 (a : real) : (term249 a) = term99.
Proof. exact (TRANS (@lem5258006 a) (@lem5258007 a)). Qed.
Lemma lem5258009 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5258010 (a : real) : (term272 a) = term273.
Proof. exact (MK_COMB (@lem5258009) (@lem5258008 a)). Qed.
Lemma lem5258011 (c : real) : (term274 c) = (term250 c).
Proof. exact (@lem1982715 term163 c). Qed.
Lemma lem5258013 (x : nat) : (real_of_num x) = (term159 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5258014 : term171 = term218.
Proof. exact (@lem5258013 term165). Qed.
Lemma lem5258016 (x : nat) : (term161 x) = (term162 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5258017 : term163 = term164.
Proof. exact (@lem5258016 term165). Qed.
Lemma lem5258018 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5258019 : term251 = term252.
Proof. exact (MK_COMB (@lem5258018) (@lem5258017)). Qed.
Lemma lem5258020 : term253 = term254.
Proof. exact (MK_COMB (@lem5258019) (@lem5258014)). Qed.
Lemma lem5258021 : term255.
Proof. exact (@lem1981473 term163 term171 term171 term171 term99 term171). Qed.
Lemma lem5258023 (m : nat) (n : nat) : (term223 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5258024 : term217 = term224.
Proof. exact (@lem5258023 (NUMERAL 0) term165). Qed.
Lemma lem5258025 : term225 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5258026 (h1 : term225 = (BIT1 0)) : term224 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5258027 : (term225 = (BIT1 0)) = (term224 = True).
Proof. exact (prop_ext (fun h1 : term225 = (BIT1 0) => @lem5258026 h1) (fun h1 : term224 = True => @lem5258025)). Qed.
Lemma lem5258028 : term224 = True.
Proof. exact (EQ_MP (@lem5258027) (@lem5258025)). Qed.
Lemma lem5258029 : term217 = True.
Proof. exact (TRANS (@lem5258024) (@lem5258028)). Qed.
Lemma lem5258030 : True = term217.
Proof. exact (SYM (@lem5258029)). Qed.
Lemma lem5258031 : term217.
Proof. exact (EQ_MP (@lem5258030) (@lem0)). Qed.
Lemma lem5258032 : term256.
Proof. exact (@lem5258021 (@lem5258031)). Qed.
Lemma lem5258034 (m : nat) (n : nat) : (term223 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5258035 : term217 = term224.
Proof. exact (@lem5258034 (NUMERAL 0) term165). Qed.
Lemma lem5258036 : term225 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5258037 (h1 : term225 = (BIT1 0)) : term224 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5258038 : (term225 = (BIT1 0)) = (term224 = True).
Proof. exact (prop_ext (fun h1 : term225 = (BIT1 0) => @lem5258037 h1) (fun h1 : term224 = True => @lem5258036)). Qed.
Lemma lem5258039 : term224 = True.
Proof. exact (EQ_MP (@lem5258038) (@lem5258036)). Qed.
Lemma lem5258040 : term217 = True.
Proof. exact (TRANS (@lem5258035) (@lem5258039)). Qed.
Lemma lem5258041 : True = term217.
Proof. exact (SYM (@lem5258040)). Qed.
Lemma lem5258042 : term217.
Proof. exact (EQ_MP (@lem5258041) (@lem0)). Qed.
Lemma lem5258043 : term257.
Proof. exact (@lem5258032 (@lem5258042)). Qed.
Lemma lem5258045 (m : nat) (n : nat) : (term223 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5258046 : term217 = term224.
Proof. exact (@lem5258045 (NUMERAL 0) term165). Qed.
Lemma lem5258047 : term225 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5258048 (h1 : term225 = (BIT1 0)) : term224 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5258049 : (term225 = (BIT1 0)) = (term224 = True).
Proof. exact (prop_ext (fun h1 : term225 = (BIT1 0) => @lem5258048 h1) (fun h1 : term224 = True => @lem5258047)). Qed.
Lemma lem5258050 : term224 = True.
Proof. exact (EQ_MP (@lem5258049) (@lem5258047)). Qed.
Lemma lem5258051 : term217 = True.
Proof. exact (TRANS (@lem5258046) (@lem5258050)). Qed.
Lemma lem5258052 : True = term217.
Proof. exact (SYM (@lem5258051)). Qed.
Lemma lem5258053 : term217.
Proof. exact (EQ_MP (@lem5258052) (@lem0)). Qed.
Lemma lem5258054 : term258.
Proof. exact (@lem5258043 (@lem5258053)). Qed.
Lemma lem5258056 (m : nat) (n : nat) : (term172 m n) = (term173 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5258057 : term174 = term175.
Proof. exact (@lem5258056 term165 term165). Qed.
Lemma lem5258058 : (term176 = (BIT1 0)) = (term177 = term165).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5258059 : term177 = term165.
Proof. exact (EQ_MP (@lem5258058) (@lem940073)). Qed.
Lemma lem5258060 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5258061 : term175 = term171.
Proof. exact (MK_COMB (@lem5258060) (@lem5258059)). Qed.
Lemma lem5258062 : term174 = term171.
Proof. exact (TRANS (@lem5258057) (@lem5258061)). Qed.
Lemma lem5258064 (m : nat) (n : nat) : (term259 m n) = (term260 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5258065 : term261 = term262.
Proof. exact (@lem5258064 term165 term165). Qed.
Lemma lem5258066 : (term176 = (BIT1 0)) = (term177 = term165).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5258067 : term177 = term165.
Proof. exact (EQ_MP (@lem5258066) (@lem940073)). Qed.
Lemma lem5258068 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5258069 : term175 = term171.
Proof. exact (MK_COMB (@lem5258068) (@lem5258067)). Qed.
Lemma lem5258070 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5258071 : term262 = term163.
Proof. exact (MK_COMB (@lem5258070) (@lem5258069)). Qed.
Lemma lem5258072 : term261 = term163.
Proof. exact (TRANS (@lem5258065) (@lem5258071)). Qed.
Lemma lem5258073 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5258074 : term263 = term251.
Proof. exact (MK_COMB (@lem5258073) (@lem5258072)). Qed.
Lemma lem5258075 : term264 = term253.
Proof. exact (MK_COMB (@lem5258074) (@lem5258062)). Qed.
Lemma lem5258077 (m : nat) : (term265 m) = term99.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5258078 : term253 = term99.
Proof. exact (@lem5258077 term165). Qed.
Lemma lem5258079 : term264 = term99.
Proof. exact (TRANS (@lem5258075) (@lem5258078)). Qed.
Lemma lem5258080 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5258081 : term266 = term267.
Proof. exact (MK_COMB (@lem5258080) (@lem5258079)). Qed.
Lemma lem5258082 : term171 = term171.
Proof. exact (eq_refl term171). Qed.
Lemma lem5258083 : term268 = term229.
Proof. exact (MK_COMB (@lem5258081) (@lem5258082)). Qed.
Lemma lem5258085 (x : nat) : (term228 x) = term99.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5258086 : term229 = term99.
Proof. exact (@lem5258085 term165). Qed.
Lemma lem5258087 : term268 = term99.
Proof. exact (TRANS (@lem5258083) (@lem5258086)). Qed.
Lemma lem5258089 (m : nat) (n : nat) : (term172 m n) = (term173 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5258090 : term174 = term175.
Proof. exact (@lem5258089 term165 term165). Qed.
Lemma lem5258091 : (term176 = (BIT1 0)) = (term177 = term165).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5258092 : term177 = term165.
Proof. exact (EQ_MP (@lem5258091) (@lem940073)). Qed.
Lemma lem5258093 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5258094 : term175 = term171.
Proof. exact (MK_COMB (@lem5258093) (@lem5258092)). Qed.
Lemma lem5258095 : term174 = term171.
Proof. exact (TRANS (@lem5258090) (@lem5258094)). Qed.
Lemma lem5258096 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem5258097 : term269 = term229.
Proof. exact (MK_COMB (@lem5258096) (@lem5258095)). Qed.
Lemma lem5258099 (x : nat) : (term228 x) = term99.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5258100 : term229 = term99.
Proof. exact (@lem5258099 term165). Qed.
Lemma lem5258101 : term269 = term99.
Proof. exact (TRANS (@lem5258097) (@lem5258100)). Qed.
Lemma lem5258102 : term99 = term269.
Proof. exact (SYM (@lem5258101)). Qed.
Lemma lem5258103 : term268 = term269.
Proof. exact (TRANS (@lem5258087) (@lem5258102)). Qed.
Lemma lem5258104 : term254 = term160.
Proof. exact (@lem5258054 (@lem5258103)). Qed.
Lemma lem5258105 : term253 = term160.
Proof. exact (TRANS (@lem5258020) (@lem5258104)). Qed.
Lemma lem5258107 (x : real) : (term181 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5258108 : term160 = term99.
Proof. exact (@lem5258107 term99). Qed.
Lemma lem5258109 : term253 = term99.
Proof. exact (TRANS (@lem5258105) (@lem5258108)). Qed.
Lemma lem5258110 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5258111 : term270 = term267.
Proof. exact (MK_COMB (@lem5258110) (@lem5258109)). Qed.
Lemma lem5258112 (c : real) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem5258113 (c : real) : (term250 c) = (term271 c).
Proof. exact (MK_COMB (@lem5258111) (@lem5258112 c)). Qed.
Lemma lem5258114 (c : real) : (term274 c) = (term271 c).
Proof. exact (TRANS (@lem5258011 c) (@lem5258113 c)). Qed.
Lemma lem5258115 (c : real) : (term271 c) = term99.
Proof. exact (@lem1982719 c). Qed.
Lemma lem5258116 (c : real) : (term274 c) = term99.
Proof. exact (TRANS (@lem5258114 c) (@lem5258115 c)). Qed.
Lemma lem5258117 (a : real) (c : real) : (term248 a c) = term275.
Proof. exact (MK_COMB (@lem5258010 a) (@lem5258116 c)). Qed.
Lemma lem5258118 (a : real) (c : real) : (term247 a c) = term275.
Proof. exact (TRANS (@lem5257902 a c) (@lem5258117 a c)). Qed.
Lemma lem5258119 : term275 = term99.
Proof. exact (@lem1982721 term99). Qed.
Lemma lem5258120 (a : real) (c : real) : (term247 a c) = term99.
Proof. exact (TRANS (@lem5258118 a c) (@lem5258119)). Qed.
Lemma lem5258121 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5258122 (a : real) (c : real) : (term276 a c) = term277.
Proof. exact (MK_COMB (@lem5258121) (@lem5258120 a c)). Qed.
Lemma lem5258123 : term99 = term99.
Proof. exact (eq_refl term99). Qed.
Lemma lem5258124 (a : real) (c : real) : (term246 a c) = term278.
Proof. exact (MK_COMB (@lem5258122 a c) (@lem5258123)). Qed.
Lemma lem5258125 (b : real) (a : real) (c : real) (h1 : term196 b a c) : term278.
Proof. exact (EQ_MP (@lem5258124 a c) (@lem5257901 b a c h1)). Qed.
Lemma lem5258127 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5258128 : term278 = term279.
Proof. exact (@lem5258127 term99 term99). Qed.
Lemma lem5258130 (x : nat) : (real_of_num x) = (term159 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5258131 : term99 = term160.
Proof. exact (@lem5258130 (NUMERAL 0)). Qed.
Lemma lem5258133 (x : nat) : (real_of_num x) = (term159 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5258134 : term99 = term160.
Proof. exact (@lem5258133 (NUMERAL 0)). Qed.
Lemma lem5258135 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5258136 : term219 = term220.
Proof. exact (MK_COMB (@lem5258135) (@lem5258134)). Qed.
Lemma lem5258137 : term279 = term280.
Proof. exact (MK_COMB (@lem5258136) (@lem5258131)). Qed.
Lemma lem5258138 : term281.
Proof. exact (@lem1980255 term99 term171 term99 term171). Qed.
Lemma lem5258140 (m : nat) (n : nat) : (term223 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5258141 : term217 = term224.
Proof. exact (@lem5258140 (NUMERAL 0) term165). Qed.
Lemma lem5258142 : term225 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5258143 (h1 : term225 = (BIT1 0)) : term224 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5258144 : (term225 = (BIT1 0)) = (term224 = True).
Proof. exact (prop_ext (fun h1 : term225 = (BIT1 0) => @lem5258143 h1) (fun h1 : term224 = True => @lem5258142)). Qed.
Lemma lem5258145 : term224 = True.
Proof. exact (EQ_MP (@lem5258144) (@lem5258142)). Qed.
Lemma lem5258146 : term217 = True.
Proof. exact (TRANS (@lem5258141) (@lem5258145)). Qed.
Lemma lem5258147 : True = term217.
Proof. exact (SYM (@lem5258146)). Qed.
Lemma lem5258148 : term217.
Proof. exact (EQ_MP (@lem5258147) (@lem0)). Qed.
Lemma lem5258149 : term282.
Proof. exact (@lem5258138 (@lem5258148)). Qed.
Lemma lem5258151 (m : nat) (n : nat) : (term223 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5258152 : term217 = term224.
Proof. exact (@lem5258151 (NUMERAL 0) term165). Qed.
Lemma lem5258153 : term225 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5258154 (h1 : term225 = (BIT1 0)) : term224 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5258155 : (term225 = (BIT1 0)) = (term224 = True).
Proof. exact (prop_ext (fun h1 : term225 = (BIT1 0) => @lem5258154 h1) (fun h1 : term224 = True => @lem5258153)). Qed.
Lemma lem5258156 : term224 = True.
Proof. exact (EQ_MP (@lem5258155) (@lem5258153)). Qed.
Lemma lem5258157 : term217 = True.
Proof. exact (TRANS (@lem5258152) (@lem5258156)). Qed.
Lemma lem5258158 : True = term217.
Proof. exact (SYM (@lem5258157)). Qed.
Lemma lem5258159 : term217.
Proof. exact (EQ_MP (@lem5258158) (@lem0)). Qed.
Lemma lem5258160 : term280 = term283.
Proof. exact (@lem5258149 (@lem5258159)). Qed.
Lemma lem5258162 (x : nat) : (term228 x) = term99.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5258163 : term229 = term99.
Proof. exact (@lem5258162 term165). Qed.
Lemma lem5258165 (x : nat) : (term228 x) = term99.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5258166 : term229 = term99.
Proof. exact (@lem5258165 term165). Qed.
Lemma lem5258167 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5258168 : term230 = term219.
Proof. exact (MK_COMB (@lem5258167) (@lem5258166)). Qed.
Lemma lem5258169 : term283 = term279.
Proof. exact (MK_COMB (@lem5258168) (@lem5258163)). Qed.
Lemma lem5258171 (m : nat) (n : nat) : (term223 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5258172 : term279 = term284.
Proof. exact (@lem5258171 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem5258173 : term284 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem5258174 : term279 = False.
Proof. exact (TRANS (@lem5258172) (@lem5258173)). Qed.
Lemma lem5258175 : term283 = False.
Proof. exact (TRANS (@lem5258169) (@lem5258174)). Qed.
Lemma lem5258176 : term280 = False.
Proof. exact (TRANS (@lem5258160) (@lem5258175)). Qed.
Lemma lem5258177 : term279 = False.
Proof. exact (TRANS (@lem5258137) (@lem5258176)). Qed.
Lemma lem5258178 : term278 = False.
Proof. exact (TRANS (@lem5258128) (@lem5258177)). Qed.
Lemma lem5258179 (b : real) (a : real) (c : real) (h1 : term196 b a c) : False.
Proof. exact (EQ_MP (@lem5258178) (@lem5258125 b a c h1)). Qed.
Lemma lem5258180 (a : real) (b : real) (c : real) (h1 : term200 a b c) : term200 a b c.
Proof. exact (h1). Qed.
Lemma lem5258181 (a : real) (b : real) (c : real) (h1 : term200 a b c) : term198 a b c.
Proof. exact (proj2 (@lem5258180 a b c h1)). Qed.
Lemma lem5258183 (a : real) (b : real) (c : real) (h1 : term200 a b c) : term120 b c.
Proof. exact (proj2 (@lem5258181 a b c h1)). Qed.
Lemma lem5258184 (a : real) (b : real) (c : real) (h1 : term200 a b c) : term102 b a c.
Proof. exact (proj1 (@lem5258181 a b c h1)). Qed.
Lemma lem5258186 (a : real) (b : real) (c : real) (h1 : term200 a b c) : term100 b c.
Proof. exact (proj1 (@lem5258184 a b c h1)). Qed.
Lemma lem5258188 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5258189 : term216 = term217.
Proof. exact (@lem5258188 term99 term171). Qed.
Lemma lem5258191 (x : nat) : (real_of_num x) = (term159 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5258192 : term171 = term218.
Proof. exact (@lem5258191 term165). Qed.
Lemma lem5258194 (x : nat) : (real_of_num x) = (term159 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5258195 : term99 = term160.
Proof. exact (@lem5258194 (NUMERAL 0)). Qed.
Lemma lem5258196 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5258197 : term219 = term220.
Proof. exact (MK_COMB (@lem5258196) (@lem5258195)). Qed.
Lemma lem5258198 : term217 = term221.
Proof. exact (MK_COMB (@lem5258197) (@lem5258192)). Qed.
Lemma lem5258199 : term222.
Proof. exact (@lem1980255 term99 term171 term171 term171). Qed.
Lemma lem5258201 (m : nat) (n : nat) : (term223 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5258202 : term217 = term224.
Proof. exact (@lem5258201 (NUMERAL 0) term165). Qed.
Lemma lem5258203 : term225 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5258204 (h1 : term225 = (BIT1 0)) : term224 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5258205 : (term225 = (BIT1 0)) = (term224 = True).
Proof. exact (prop_ext (fun h1 : term225 = (BIT1 0) => @lem5258204 h1) (fun h1 : term224 = True => @lem5258203)). Qed.
Lemma lem5258206 : term224 = True.
Proof. exact (EQ_MP (@lem5258205) (@lem5258203)). Qed.
Lemma lem5258207 : term217 = True.
Proof. exact (TRANS (@lem5258202) (@lem5258206)). Qed.
Lemma lem5258208 : True = term217.
Proof. exact (SYM (@lem5258207)). Qed.
Lemma lem5258209 : term217.
Proof. exact (EQ_MP (@lem5258208) (@lem0)). Qed.
Lemma lem5258210 : term226.
Proof. exact (@lem5258199 (@lem5258209)). Qed.
Lemma lem5258212 (m : nat) (n : nat) : (term223 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5258213 : term217 = term224.
Proof. exact (@lem5258212 (NUMERAL 0) term165). Qed.
Lemma lem5258214 : term225 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5258215 (h1 : term225 = (BIT1 0)) : term224 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5258216 : (term225 = (BIT1 0)) = (term224 = True).
Proof. exact (prop_ext (fun h1 : term225 = (BIT1 0) => @lem5258215 h1) (fun h1 : term224 = True => @lem5258214)). Qed.
Lemma lem5258217 : term224 = True.
Proof. exact (EQ_MP (@lem5258216) (@lem5258214)). Qed.
Lemma lem5258218 : term217 = True.
Proof. exact (TRANS (@lem5258213) (@lem5258217)). Qed.
Lemma lem5258219 : True = term217.
Proof. exact (SYM (@lem5258218)). Qed.
Lemma lem5258220 : term217.
Proof. exact (EQ_MP (@lem5258219) (@lem0)). Qed.
Lemma lem5258221 : term221 = term227.
Proof. exact (@lem5258210 (@lem5258220)). Qed.
Lemma lem5258223 (m : nat) (n : nat) : (term172 m n) = (term173 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5258224 : term174 = term175.
Proof. exact (@lem5258223 term165 term165). Qed.
Lemma lem5258225 : (term176 = (BIT1 0)) = (term177 = term165).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5258226 : term177 = term165.
Proof. exact (EQ_MP (@lem5258225) (@lem940073)). Qed.
Lemma lem5258227 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5258228 : term175 = term171.
Proof. exact (MK_COMB (@lem5258227) (@lem5258226)). Qed.
Lemma lem5258229 : term174 = term171.
Proof. exact (TRANS (@lem5258224) (@lem5258228)). Qed.
Lemma lem5258231 (x : nat) : (term228 x) = term99.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5258232 : term229 = term99.
Proof. exact (@lem5258231 term165). Qed.
Lemma lem5258233 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5258234 : term230 = term219.
Proof. exact (MK_COMB (@lem5258233) (@lem5258232)). Qed.
Lemma lem5258235 : term227 = term217.
Proof. exact (MK_COMB (@lem5258234) (@lem5258229)). Qed.
Lemma lem5258237 (m : nat) (n : nat) : (term223 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5258238 : term217 = term224.
Proof. exact (@lem5258237 (NUMERAL 0) term165). Qed.
Lemma lem5258239 : term225 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5258240 (h1 : term225 = (BIT1 0)) : term224 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5258241 : (term225 = (BIT1 0)) = (term224 = True).
Proof. exact (prop_ext (fun h1 : term225 = (BIT1 0) => @lem5258240 h1) (fun h1 : term224 = True => @lem5258239)). Qed.
Lemma lem5258242 : term224 = True.
Proof. exact (EQ_MP (@lem5258241) (@lem5258239)). Qed.
Lemma lem5258243 : term217 = True.
Proof. exact (TRANS (@lem5258238) (@lem5258242)). Qed.
Lemma lem5258244 : term227 = True.
Proof. exact (TRANS (@lem5258235) (@lem5258243)). Qed.
Lemma lem5258245 : term221 = True.
Proof. exact (TRANS (@lem5258221) (@lem5258244)). Qed.
Lemma lem5258246 : term217 = True.
Proof. exact (TRANS (@lem5258198) (@lem5258245)). Qed.
Lemma lem5258247 : term216 = True.
Proof. exact (TRANS (@lem5258189) (@lem5258246)). Qed.
Lemma lem5258248 : True = term216.
Proof. exact (SYM (@lem5258247)). Qed.
Lemma lem5258249 : term216.
Proof. exact (EQ_MP (@lem5258248) (@lem0)). Qed.
Lemma lem5258250 (a : real) (b : real) (c : real) (h1 : term200 a b c) : term231 b c.
Proof. exact (conj (@lem5258249) (@lem5258186 a b c h1)). Qed.
Lemma lem5258252 (x : real) (y : real) : term232 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5258253 (b : real) (c : real) : term233 b c.
Proof. exact (@lem5258252 term171 (term96 b c)). Qed.
Lemma lem5258254 (a : real) (b : real) (c : real) (h1 : term200 a b c) : term234 b c.
Proof. exact (@lem5258253 b c (@lem5258250 a b c h1)). Qed.
Lemma lem5258255 (b : real) (c : real) : (term235 b c) = (term96 b c).
Proof. exact (@lem1982733 (term96 b c)). Qed.
Lemma lem5258256 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5258257 (b : real) (c : real) : (term236 b c) = (term98 b c).
Proof. exact (MK_COMB (@lem5258256) (@lem5258255 b c)). Qed.
Lemma lem5258258 : term99 = term99.
Proof. exact (eq_refl term99). Qed.
Lemma lem5258259 (b : real) (c : real) : (term234 b c) = (term100 b c).
Proof. exact (MK_COMB (@lem5258257 b c) (@lem5258258)). Qed.
Lemma lem5258260 (a : real) (b : real) (c : real) (h1 : term200 a b c) : term100 b c.
Proof. exact (EQ_MP (@lem5258259 b c) (@lem5258254 a b c h1)). Qed.
Lemma lem5258262 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5258263 : term216 = term217.
Proof. exact (@lem5258262 term99 term171). Qed.
Lemma lem5258265 (x : nat) : (real_of_num x) = (term159 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5258266 : term171 = term218.
Proof. exact (@lem5258265 term165). Qed.
Lemma lem5258268 (x : nat) : (real_of_num x) = (term159 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5258269 : term99 = term160.
Proof. exact (@lem5258268 (NUMERAL 0)). Qed.
Lemma lem5258270 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5258271 : term219 = term220.
Proof. exact (MK_COMB (@lem5258270) (@lem5258269)). Qed.
Lemma lem5258272 : term217 = term221.
Proof. exact (MK_COMB (@lem5258271) (@lem5258266)). Qed.
Lemma lem5258273 : term222.
Proof. exact (@lem1980255 term99 term171 term171 term171). Qed.
Lemma lem5258275 (m : nat) (n : nat) : (term223 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5258276 : term217 = term224.
Proof. exact (@lem5258275 (NUMERAL 0) term165). Qed.
Lemma lem5258277 : term225 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5258278 (h1 : term225 = (BIT1 0)) : term224 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5258279 : (term225 = (BIT1 0)) = (term224 = True).
Proof. exact (prop_ext (fun h1 : term225 = (BIT1 0) => @lem5258278 h1) (fun h1 : term224 = True => @lem5258277)). Qed.
Lemma lem5258280 : term224 = True.
Proof. exact (EQ_MP (@lem5258279) (@lem5258277)). Qed.
Lemma lem5258281 : term217 = True.
Proof. exact (TRANS (@lem5258276) (@lem5258280)). Qed.
Lemma lem5258282 : True = term217.
Proof. exact (SYM (@lem5258281)). Qed.
Lemma lem5258283 : term217.
Proof. exact (EQ_MP (@lem5258282) (@lem0)). Qed.
Lemma lem5258284 : term226.
Proof. exact (@lem5258273 (@lem5258283)). Qed.
Lemma lem5258286 (m : nat) (n : nat) : (term223 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5258287 : term217 = term224.
Proof. exact (@lem5258286 (NUMERAL 0) term165). Qed.
Lemma lem5258288 : term225 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5258289 (h1 : term225 = (BIT1 0)) : term224 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5258290 : (term225 = (BIT1 0)) = (term224 = True).
Proof. exact (prop_ext (fun h1 : term225 = (BIT1 0) => @lem5258289 h1) (fun h1 : term224 = True => @lem5258288)). Qed.
Lemma lem5258291 : term224 = True.
Proof. exact (EQ_MP (@lem5258290) (@lem5258288)). Qed.
Lemma lem5258292 : term217 = True.
Proof. exact (TRANS (@lem5258287) (@lem5258291)). Qed.
Lemma lem5258293 : True = term217.
Proof. exact (SYM (@lem5258292)). Qed.
Lemma lem5258294 : term217.
Proof. exact (EQ_MP (@lem5258293) (@lem0)). Qed.
Lemma lem5258295 : term221 = term227.
Proof. exact (@lem5258284 (@lem5258294)). Qed.
Lemma lem5258297 (m : nat) (n : nat) : (term172 m n) = (term173 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5258298 : term174 = term175.
Proof. exact (@lem5258297 term165 term165). Qed.
Lemma lem5258299 : (term176 = (BIT1 0)) = (term177 = term165).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5258300 : term177 = term165.
Proof. exact (EQ_MP (@lem5258299) (@lem940073)). Qed.
Lemma lem5258301 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5258302 : term175 = term171.
Proof. exact (MK_COMB (@lem5258301) (@lem5258300)). Qed.
Lemma lem5258303 : term174 = term171.
Proof. exact (TRANS (@lem5258298) (@lem5258302)). Qed.
Lemma lem5258305 (x : nat) : (term228 x) = term99.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5258306 : term229 = term99.
Proof. exact (@lem5258305 term165). Qed.
Lemma lem5258307 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5258308 : term230 = term219.
Proof. exact (MK_COMB (@lem5258307) (@lem5258306)). Qed.
Lemma lem5258309 : term227 = term217.
Proof. exact (MK_COMB (@lem5258308) (@lem5258303)). Qed.
Lemma lem5258311 (m : nat) (n : nat) : (term223 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5258312 : term217 = term224.
Proof. exact (@lem5258311 (NUMERAL 0) term165). Qed.
Lemma lem5258313 : term225 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5258314 (h1 : term225 = (BIT1 0)) : term224 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5258315 : (term225 = (BIT1 0)) = (term224 = True).
Proof. exact (prop_ext (fun h1 : term225 = (BIT1 0) => @lem5258314 h1) (fun h1 : term224 = True => @lem5258313)). Qed.
Lemma lem5258316 : term224 = True.
Proof. exact (EQ_MP (@lem5258315) (@lem5258313)). Qed.
Lemma lem5258317 : term217 = True.
Proof. exact (TRANS (@lem5258312) (@lem5258316)). Qed.
Lemma lem5258318 : term227 = True.
Proof. exact (TRANS (@lem5258309) (@lem5258317)). Qed.
Lemma lem5258319 : term221 = True.
Proof. exact (TRANS (@lem5258295) (@lem5258318)). Qed.
Lemma lem5258320 : term217 = True.
Proof. exact (TRANS (@lem5258272) (@lem5258319)). Qed.
Lemma lem5258321 : term216 = True.
Proof. exact (TRANS (@lem5258263) (@lem5258320)). Qed.
Lemma lem5258322 : True = term216.
Proof. exact (SYM (@lem5258321)). Qed.
Lemma lem5258323 : term216.
Proof. exact (EQ_MP (@lem5258322) (@lem0)). Qed.
Lemma lem5258324 (a : real) (b : real) (c : real) (h1 : term200 a b c) : term237 b c.
Proof. exact (conj (@lem5258323) (@lem5258183 a b c h1)). Qed.
Lemma lem5258326 (x : real) (y : real) : term238 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem5258327 (b : real) (c : real) : term239 b c.
Proof. exact (@lem5258326 term171 (term116 b c)). Qed.
Lemma lem5258328 (a : real) (b : real) (c : real) (h1 : term200 a b c) : term240 b c.
Proof. exact (@lem5258327 b c (@lem5258324 a b c h1)). Qed.
Lemma lem5258329 (b : real) (c : real) : (term241 b c) = (term116 b c).
Proof. exact (@lem1982733 (term116 b c)). Qed.
Lemma lem5258330 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5258331 (b : real) (c : real) : (term242 b c) = (term119 b c).
Proof. exact (MK_COMB (@lem5258330) (@lem5258329 b c)). Qed.
Lemma lem5258332 : term99 = term99.
Proof. exact (eq_refl term99). Qed.
Lemma lem5258333 (b : real) (c : real) : (term240 b c) = (term120 b c).
Proof. exact (MK_COMB (@lem5258331 b c) (@lem5258332)). Qed.
Lemma lem5258334 (a : real) (b : real) (c : real) (h1 : term200 a b c) : term120 b c.
Proof. exact (EQ_MP (@lem5258333 b c) (@lem5258328 a b c h1)). Qed.
Lemma lem5258335 (a : real) (b : real) (c : real) (h1 : term200 a b c) : term243 b c.
Proof. exact (conj (@lem5258334 a b c h1) (@lem5258260 a b c h1)). Qed.
Lemma lem5258337 (x : real) (y : real) : term244 x y.
Proof. exact (proj1 (@lem1988348 x y)). Qed.
Lemma lem5258338 (b : real) (c : real) : term245 b c.
Proof. exact (@lem5258337 (term116 b c) (term96 b c)). Qed.
Lemma lem5258339 (a : real) (b : real) (c : real) (h1 : term200 a b c) : term246 b c.
Proof. exact (@lem5258338 b c (@lem5258335 a b c h1)). Qed.
Lemma lem5258340 (b : real) (c : real) : (term247 b c) = (term248 b c).
Proof. exact (@lem1982753 (term117 b) b c (term117 c)). Qed.
Lemma lem5258341 (b : real) : (term249 b) = (term250 b).
Proof. exact (@lem1982713 term163 b). Qed.
Lemma lem5258343 (x : nat) : (real_of_num x) = (term159 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5258344 : term171 = term218.
Proof. exact (@lem5258343 term165). Qed.
Lemma lem5258346 (x : nat) : (term161 x) = (term162 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5258347 : term163 = term164.
Proof. exact (@lem5258346 term165). Qed.
Lemma lem5258348 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5258349 : term251 = term252.
Proof. exact (MK_COMB (@lem5258348) (@lem5258347)). Qed.
Lemma lem5258350 : term253 = term254.
Proof. exact (MK_COMB (@lem5258349) (@lem5258344)). Qed.
Lemma lem5258351 : term255.
Proof. exact (@lem1981473 term163 term171 term171 term171 term99 term171). Qed.
Lemma lem5258353 (m : nat) (n : nat) : (term223 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5258354 : term217 = term224.
Proof. exact (@lem5258353 (NUMERAL 0) term165). Qed.
Lemma lem5258355 : term225 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5258356 (h1 : term225 = (BIT1 0)) : term224 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5258357 : (term225 = (BIT1 0)) = (term224 = True).
Proof. exact (prop_ext (fun h1 : term225 = (BIT1 0) => @lem5258356 h1) (fun h1 : term224 = True => @lem5258355)). Qed.
Lemma lem5258358 : term224 = True.
Proof. exact (EQ_MP (@lem5258357) (@lem5258355)). Qed.
Lemma lem5258359 : term217 = True.
Proof. exact (TRANS (@lem5258354) (@lem5258358)). Qed.
Lemma lem5258360 : True = term217.
Proof. exact (SYM (@lem5258359)). Qed.
Lemma lem5258361 : term217.
Proof. exact (EQ_MP (@lem5258360) (@lem0)). Qed.
Lemma lem5258362 : term256.
Proof. exact (@lem5258351 (@lem5258361)). Qed.
Lemma lem5258364 (m : nat) (n : nat) : (term223 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5258365 : term217 = term224.
Proof. exact (@lem5258364 (NUMERAL 0) term165). Qed.
Lemma lem5258366 : term225 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5258367 (h1 : term225 = (BIT1 0)) : term224 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5258368 : (term225 = (BIT1 0)) = (term224 = True).
Proof. exact (prop_ext (fun h1 : term225 = (BIT1 0) => @lem5258367 h1) (fun h1 : term224 = True => @lem5258366)). Qed.
Lemma lem5258369 : term224 = True.
Proof. exact (EQ_MP (@lem5258368) (@lem5258366)). Qed.
Lemma lem5258370 : term217 = True.
Proof. exact (TRANS (@lem5258365) (@lem5258369)). Qed.
Lemma lem5258371 : True = term217.
Proof. exact (SYM (@lem5258370)). Qed.
Lemma lem5258372 : term217.
Proof. exact (EQ_MP (@lem5258371) (@lem0)). Qed.
Lemma lem5258373 : term257.
Proof. exact (@lem5258362 (@lem5258372)). Qed.
Lemma lem5258375 (m : nat) (n : nat) : (term223 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5258376 : term217 = term224.
Proof. exact (@lem5258375 (NUMERAL 0) term165). Qed.
Lemma lem5258377 : term225 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5258378 (h1 : term225 = (BIT1 0)) : term224 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5258379 : (term225 = (BIT1 0)) = (term224 = True).
Proof. exact (prop_ext (fun h1 : term225 = (BIT1 0) => @lem5258378 h1) (fun h1 : term224 = True => @lem5258377)). Qed.
Lemma lem5258380 : term224 = True.
Proof. exact (EQ_MP (@lem5258379) (@lem5258377)). Qed.
Lemma lem5258381 : term217 = True.
Proof. exact (TRANS (@lem5258376) (@lem5258380)). Qed.
Lemma lem5258382 : True = term217.
Proof. exact (SYM (@lem5258381)). Qed.
Lemma lem5258383 : term217.
Proof. exact (EQ_MP (@lem5258382) (@lem0)). Qed.
Lemma lem5258384 : term258.
Proof. exact (@lem5258373 (@lem5258383)). Qed.
Lemma lem5258386 (m : nat) (n : nat) : (term172 m n) = (term173 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5258387 : term174 = term175.
Proof. exact (@lem5258386 term165 term165). Qed.
Lemma lem5258388 : (term176 = (BIT1 0)) = (term177 = term165).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5258389 : term177 = term165.
Proof. exact (EQ_MP (@lem5258388) (@lem940073)). Qed.
Lemma lem5258390 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5258391 : term175 = term171.
Proof. exact (MK_COMB (@lem5258390) (@lem5258389)). Qed.
Lemma lem5258392 : term174 = term171.
Proof. exact (TRANS (@lem5258387) (@lem5258391)). Qed.
Lemma lem5258394 (m : nat) (n : nat) : (term259 m n) = (term260 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5258395 : term261 = term262.
Proof. exact (@lem5258394 term165 term165). Qed.
Lemma lem5258396 : (term176 = (BIT1 0)) = (term177 = term165).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5258397 : term177 = term165.
Proof. exact (EQ_MP (@lem5258396) (@lem940073)). Qed.
Lemma lem5258398 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5258399 : term175 = term171.
Proof. exact (MK_COMB (@lem5258398) (@lem5258397)). Qed.
Lemma lem5258400 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5258401 : term262 = term163.
Proof. exact (MK_COMB (@lem5258400) (@lem5258399)). Qed.
Lemma lem5258402 : term261 = term163.
Proof. exact (TRANS (@lem5258395) (@lem5258401)). Qed.
Lemma lem5258403 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5258404 : term263 = term251.
Proof. exact (MK_COMB (@lem5258403) (@lem5258402)). Qed.
Lemma lem5258405 : term264 = term253.
Proof. exact (MK_COMB (@lem5258404) (@lem5258392)). Qed.
Lemma lem5258407 (m : nat) : (term265 m) = term99.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5258408 : term253 = term99.
Proof. exact (@lem5258407 term165). Qed.
Lemma lem5258409 : term264 = term99.
Proof. exact (TRANS (@lem5258405) (@lem5258408)). Qed.
Lemma lem5258410 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5258411 : term266 = term267.
Proof. exact (MK_COMB (@lem5258410) (@lem5258409)). Qed.
Lemma lem5258412 : term171 = term171.
Proof. exact (eq_refl term171). Qed.
Lemma lem5258413 : term268 = term229.
Proof. exact (MK_COMB (@lem5258411) (@lem5258412)). Qed.
Lemma lem5258415 (x : nat) : (term228 x) = term99.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5258416 : term229 = term99.
Proof. exact (@lem5258415 term165). Qed.
Lemma lem5258417 : term268 = term99.
Proof. exact (TRANS (@lem5258413) (@lem5258416)). Qed.
Lemma lem5258419 (m : nat) (n : nat) : (term172 m n) = (term173 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5258420 : term174 = term175.
Proof. exact (@lem5258419 term165 term165). Qed.
Lemma lem5258421 : (term176 = (BIT1 0)) = (term177 = term165).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5258422 : term177 = term165.
Proof. exact (EQ_MP (@lem5258421) (@lem940073)). Qed.
Lemma lem5258423 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5258424 : term175 = term171.
Proof. exact (MK_COMB (@lem5258423) (@lem5258422)). Qed.
Lemma lem5258425 : term174 = term171.
Proof. exact (TRANS (@lem5258420) (@lem5258424)). Qed.
Lemma lem5258426 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem5258427 : term269 = term229.
Proof. exact (MK_COMB (@lem5258426) (@lem5258425)). Qed.
Lemma lem5258429 (x : nat) : (term228 x) = term99.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5258430 : term229 = term99.
Proof. exact (@lem5258429 term165). Qed.
Lemma lem5258431 : term269 = term99.
Proof. exact (TRANS (@lem5258427) (@lem5258430)). Qed.
Lemma lem5258432 : term99 = term269.
Proof. exact (SYM (@lem5258431)). Qed.
Lemma lem5258433 : term268 = term269.
Proof. exact (TRANS (@lem5258417) (@lem5258432)). Qed.
Lemma lem5258434 : term254 = term160.
Proof. exact (@lem5258384 (@lem5258433)). Qed.
Lemma lem5258435 : term253 = term160.
Proof. exact (TRANS (@lem5258350) (@lem5258434)). Qed.
Lemma lem5258437 (x : real) : (term181 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5258438 : term160 = term99.
Proof. exact (@lem5258437 term99). Qed.
Lemma lem5258439 : term253 = term99.
Proof. exact (TRANS (@lem5258435) (@lem5258438)). Qed.
Lemma lem5258440 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5258441 : term270 = term267.
Proof. exact (MK_COMB (@lem5258440) (@lem5258439)). Qed.
Lemma lem5258442 (b : real) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem5258443 (b : real) : (term250 b) = (term271 b).
Proof. exact (MK_COMB (@lem5258441) (@lem5258442 b)). Qed.
Lemma lem5258444 (b : real) : (term249 b) = (term271 b).
Proof. exact (TRANS (@lem5258341 b) (@lem5258443 b)). Qed.
Lemma lem5258445 (b : real) : (term271 b) = term99.
Proof. exact (@lem1982719 b). Qed.
Lemma lem5258446 (b : real) : (term249 b) = term99.
Proof. exact (TRANS (@lem5258444 b) (@lem5258445 b)). Qed.
Lemma lem5258447 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5258448 (b : real) : (term272 b) = term273.
Proof. exact (MK_COMB (@lem5258447) (@lem5258446 b)). Qed.
Lemma lem5258449 (c : real) : (term274 c) = (term250 c).
Proof. exact (@lem1982715 term163 c). Qed.
Lemma lem5258451 (x : nat) : (real_of_num x) = (term159 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5258452 : term171 = term218.
Proof. exact (@lem5258451 term165). Qed.
Lemma lem5258454 (x : nat) : (term161 x) = (term162 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5258455 : term163 = term164.
Proof. exact (@lem5258454 term165). Qed.
Lemma lem5258456 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5258457 : term251 = term252.
Proof. exact (MK_COMB (@lem5258456) (@lem5258455)). Qed.
Lemma lem5258458 : term253 = term254.
Proof. exact (MK_COMB (@lem5258457) (@lem5258452)). Qed.
Lemma lem5258459 : term255.
Proof. exact (@lem1981473 term163 term171 term171 term171 term99 term171). Qed.
Lemma lem5258461 (m : nat) (n : nat) : (term223 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5258462 : term217 = term224.
Proof. exact (@lem5258461 (NUMERAL 0) term165). Qed.
Lemma lem5258463 : term225 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5258464 (h1 : term225 = (BIT1 0)) : term224 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5258465 : (term225 = (BIT1 0)) = (term224 = True).
Proof. exact (prop_ext (fun h1 : term225 = (BIT1 0) => @lem5258464 h1) (fun h1 : term224 = True => @lem5258463)). Qed.
Lemma lem5258466 : term224 = True.
Proof. exact (EQ_MP (@lem5258465) (@lem5258463)). Qed.
Lemma lem5258467 : term217 = True.
Proof. exact (TRANS (@lem5258462) (@lem5258466)). Qed.
Lemma lem5258468 : True = term217.
Proof. exact (SYM (@lem5258467)). Qed.
Lemma lem5258469 : term217.
Proof. exact (EQ_MP (@lem5258468) (@lem0)). Qed.
Lemma lem5258470 : term256.
Proof. exact (@lem5258459 (@lem5258469)). Qed.
Lemma lem5258472 (m : nat) (n : nat) : (term223 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5258473 : term217 = term224.
Proof. exact (@lem5258472 (NUMERAL 0) term165). Qed.
Lemma lem5258474 : term225 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5258475 (h1 : term225 = (BIT1 0)) : term224 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5258476 : (term225 = (BIT1 0)) = (term224 = True).
Proof. exact (prop_ext (fun h1 : term225 = (BIT1 0) => @lem5258475 h1) (fun h1 : term224 = True => @lem5258474)). Qed.
Lemma lem5258477 : term224 = True.
Proof. exact (EQ_MP (@lem5258476) (@lem5258474)). Qed.
Lemma lem5258478 : term217 = True.
Proof. exact (TRANS (@lem5258473) (@lem5258477)). Qed.
Lemma lem5258479 : True = term217.
Proof. exact (SYM (@lem5258478)). Qed.
Lemma lem5258480 : term217.
Proof. exact (EQ_MP (@lem5258479) (@lem0)). Qed.
Lemma lem5258481 : term257.
Proof. exact (@lem5258470 (@lem5258480)). Qed.
Lemma lem5258483 (m : nat) (n : nat) : (term223 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5258484 : term217 = term224.
Proof. exact (@lem5258483 (NUMERAL 0) term165). Qed.
Lemma lem5258485 : term225 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5258486 (h1 : term225 = (BIT1 0)) : term224 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5258487 : (term225 = (BIT1 0)) = (term224 = True).
Proof. exact (prop_ext (fun h1 : term225 = (BIT1 0) => @lem5258486 h1) (fun h1 : term224 = True => @lem5258485)). Qed.
Lemma lem5258488 : term224 = True.
Proof. exact (EQ_MP (@lem5258487) (@lem5258485)). Qed.
Lemma lem5258489 : term217 = True.
Proof. exact (TRANS (@lem5258484) (@lem5258488)). Qed.
Lemma lem5258490 : True = term217.
Proof. exact (SYM (@lem5258489)). Qed.
Lemma lem5258491 : term217.
Proof. exact (EQ_MP (@lem5258490) (@lem0)). Qed.
Lemma lem5258492 : term258.
Proof. exact (@lem5258481 (@lem5258491)). Qed.
Lemma lem5258494 (m : nat) (n : nat) : (term172 m n) = (term173 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5258495 : term174 = term175.
Proof. exact (@lem5258494 term165 term165). Qed.
Lemma lem5258496 : (term176 = (BIT1 0)) = (term177 = term165).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5258497 : term177 = term165.
Proof. exact (EQ_MP (@lem5258496) (@lem940073)). Qed.
Lemma lem5258498 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5258499 : term175 = term171.
Proof. exact (MK_COMB (@lem5258498) (@lem5258497)). Qed.
Lemma lem5258500 : term174 = term171.
Proof. exact (TRANS (@lem5258495) (@lem5258499)). Qed.
Lemma lem5258502 (m : nat) (n : nat) : (term259 m n) = (term260 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5258503 : term261 = term262.
Proof. exact (@lem5258502 term165 term165). Qed.
Lemma lem5258504 : (term176 = (BIT1 0)) = (term177 = term165).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5258505 : term177 = term165.
Proof. exact (EQ_MP (@lem5258504) (@lem940073)). Qed.
Lemma lem5258506 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5258507 : term175 = term171.
Proof. exact (MK_COMB (@lem5258506) (@lem5258505)). Qed.
Lemma lem5258508 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5258509 : term262 = term163.
Proof. exact (MK_COMB (@lem5258508) (@lem5258507)). Qed.
Lemma lem5258510 : term261 = term163.
Proof. exact (TRANS (@lem5258503) (@lem5258509)). Qed.
Lemma lem5258511 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5258512 : term263 = term251.
Proof. exact (MK_COMB (@lem5258511) (@lem5258510)). Qed.
Lemma lem5258513 : term264 = term253.
Proof. exact (MK_COMB (@lem5258512) (@lem5258500)). Qed.
Lemma lem5258515 (m : nat) : (term265 m) = term99.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5258516 : term253 = term99.
Proof. exact (@lem5258515 term165). Qed.
Lemma lem5258517 : term264 = term99.
Proof. exact (TRANS (@lem5258513) (@lem5258516)). Qed.
Lemma lem5258518 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5258519 : term266 = term267.
Proof. exact (MK_COMB (@lem5258518) (@lem5258517)). Qed.
Lemma lem5258520 : term171 = term171.
Proof. exact (eq_refl term171). Qed.
Lemma lem5258521 : term268 = term229.
Proof. exact (MK_COMB (@lem5258519) (@lem5258520)). Qed.
Lemma lem5258523 (x : nat) : (term228 x) = term99.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5258524 : term229 = term99.
Proof. exact (@lem5258523 term165). Qed.
Lemma lem5258525 : term268 = term99.
Proof. exact (TRANS (@lem5258521) (@lem5258524)). Qed.
Lemma lem5258527 (m : nat) (n : nat) : (term172 m n) = (term173 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5258528 : term174 = term175.
Proof. exact (@lem5258527 term165 term165). Qed.
Lemma lem5258529 : (term176 = (BIT1 0)) = (term177 = term165).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5258530 : term177 = term165.
Proof. exact (EQ_MP (@lem5258529) (@lem940073)). Qed.
Lemma lem5258531 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5258532 : term175 = term171.
Proof. exact (MK_COMB (@lem5258531) (@lem5258530)). Qed.
Lemma lem5258533 : term174 = term171.
Proof. exact (TRANS (@lem5258528) (@lem5258532)). Qed.
Lemma lem5258534 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem5258535 : term269 = term229.
Proof. exact (MK_COMB (@lem5258534) (@lem5258533)). Qed.
Lemma lem5258537 (x : nat) : (term228 x) = term99.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5258538 : term229 = term99.
Proof. exact (@lem5258537 term165). Qed.
Lemma lem5258539 : term269 = term99.
Proof. exact (TRANS (@lem5258535) (@lem5258538)). Qed.
Lemma lem5258540 : term99 = term269.
Proof. exact (SYM (@lem5258539)). Qed.
Lemma lem5258541 : term268 = term269.
Proof. exact (TRANS (@lem5258525) (@lem5258540)). Qed.
Lemma lem5258542 : term254 = term160.
Proof. exact (@lem5258492 (@lem5258541)). Qed.
Lemma lem5258543 : term253 = term160.
Proof. exact (TRANS (@lem5258458) (@lem5258542)). Qed.
Lemma lem5258545 (x : real) : (term181 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5258546 : term160 = term99.
Proof. exact (@lem5258545 term99). Qed.
Lemma lem5258547 : term253 = term99.
Proof. exact (TRANS (@lem5258543) (@lem5258546)). Qed.
Lemma lem5258548 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5258549 : term270 = term267.
Proof. exact (MK_COMB (@lem5258548) (@lem5258547)). Qed.
Lemma lem5258550 (c : real) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem5258551 (c : real) : (term250 c) = (term271 c).
Proof. exact (MK_COMB (@lem5258549) (@lem5258550 c)). Qed.
Lemma lem5258552 (c : real) : (term274 c) = (term271 c).
Proof. exact (TRANS (@lem5258449 c) (@lem5258551 c)). Qed.
Lemma lem5258553 (c : real) : (term271 c) = term99.
Proof. exact (@lem1982719 c). Qed.
Lemma lem5258554 (c : real) : (term274 c) = term99.
Proof. exact (TRANS (@lem5258552 c) (@lem5258553 c)). Qed.
Lemma lem5258555 (b : real) (c : real) : (term248 b c) = term275.
Proof. exact (MK_COMB (@lem5258448 b) (@lem5258554 c)). Qed.
Lemma lem5258556 (b : real) (c : real) : (term247 b c) = term275.
Proof. exact (TRANS (@lem5258340 b c) (@lem5258555 b c)). Qed.
Lemma lem5258557 : term275 = term99.
Proof. exact (@lem1982721 term99). Qed.
Lemma lem5258558 (b : real) (c : real) : (term247 b c) = term99.
Proof. exact (TRANS (@lem5258556 b c) (@lem5258557)). Qed.
Lemma lem5258559 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5258560 (b : real) (c : real) : (term276 b c) = term277.
Proof. exact (MK_COMB (@lem5258559) (@lem5258558 b c)). Qed.
Lemma lem5258561 : term99 = term99.
Proof. exact (eq_refl term99). Qed.
Lemma lem5258562 (b : real) (c : real) : (term246 b c) = term278.
Proof. exact (MK_COMB (@lem5258560 b c) (@lem5258561)). Qed.
Lemma lem5258563 (a : real) (b : real) (c : real) (h1 : term200 a b c) : term278.
Proof. exact (EQ_MP (@lem5258562 b c) (@lem5258339 a b c h1)). Qed.
Lemma lem5258565 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5258566 : term278 = term279.
Proof. exact (@lem5258565 term99 term99). Qed.
Lemma lem5258568 (x : nat) : (real_of_num x) = (term159 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5258569 : term99 = term160.
Proof. exact (@lem5258568 (NUMERAL 0)). Qed.
Lemma lem5258571 (x : nat) : (real_of_num x) = (term159 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5258572 : term99 = term160.
Proof. exact (@lem5258571 (NUMERAL 0)). Qed.
Lemma lem5258573 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5258574 : term219 = term220.
Proof. exact (MK_COMB (@lem5258573) (@lem5258572)). Qed.
Lemma lem5258575 : term279 = term280.
Proof. exact (MK_COMB (@lem5258574) (@lem5258569)). Qed.
Lemma lem5258576 : term281.
Proof. exact (@lem1980255 term99 term171 term99 term171). Qed.
Lemma lem5258578 (m : nat) (n : nat) : (term223 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5258579 : term217 = term224.
Proof. exact (@lem5258578 (NUMERAL 0) term165). Qed.
Lemma lem5258580 : term225 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5258581 (h1 : term225 = (BIT1 0)) : term224 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5258582 : (term225 = (BIT1 0)) = (term224 = True).
Proof. exact (prop_ext (fun h1 : term225 = (BIT1 0) => @lem5258581 h1) (fun h1 : term224 = True => @lem5258580)). Qed.
Lemma lem5258583 : term224 = True.
Proof. exact (EQ_MP (@lem5258582) (@lem5258580)). Qed.
Lemma lem5258584 : term217 = True.
Proof. exact (TRANS (@lem5258579) (@lem5258583)). Qed.
Lemma lem5258585 : True = term217.
Proof. exact (SYM (@lem5258584)). Qed.
Lemma lem5258586 : term217.
Proof. exact (EQ_MP (@lem5258585) (@lem0)). Qed.
Lemma lem5258587 : term282.
Proof. exact (@lem5258576 (@lem5258586)). Qed.
Lemma lem5258589 (m : nat) (n : nat) : (term223 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5258590 : term217 = term224.
Proof. exact (@lem5258589 (NUMERAL 0) term165). Qed.
Lemma lem5258591 : term225 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5258592 (h1 : term225 = (BIT1 0)) : term224 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5258593 : (term225 = (BIT1 0)) = (term224 = True).
Proof. exact (prop_ext (fun h1 : term225 = (BIT1 0) => @lem5258592 h1) (fun h1 : term224 = True => @lem5258591)). Qed.
Lemma lem5258594 : term224 = True.
Proof. exact (EQ_MP (@lem5258593) (@lem5258591)). Qed.
Lemma lem5258595 : term217 = True.
Proof. exact (TRANS (@lem5258590) (@lem5258594)). Qed.
Lemma lem5258596 : True = term217.
Proof. exact (SYM (@lem5258595)). Qed.
Lemma lem5258597 : term217.
Proof. exact (EQ_MP (@lem5258596) (@lem0)). Qed.
Lemma lem5258598 : term280 = term283.
Proof. exact (@lem5258587 (@lem5258597)). Qed.
Lemma lem5258600 (x : nat) : (term228 x) = term99.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5258601 : term229 = term99.
Proof. exact (@lem5258600 term165). Qed.
Lemma lem5258603 (x : nat) : (term228 x) = term99.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5258604 : term229 = term99.
Proof. exact (@lem5258603 term165). Qed.
Lemma lem5258605 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5258606 : term230 = term219.
Proof. exact (MK_COMB (@lem5258605) (@lem5258604)). Qed.
Lemma lem5258607 : term283 = term279.
Proof. exact (MK_COMB (@lem5258606) (@lem5258601)). Qed.
Lemma lem5258609 (m : nat) (n : nat) : (term223 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5258610 : term279 = term284.
Proof. exact (@lem5258609 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem5258611 : term284 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem5258612 : term279 = False.
Proof. exact (TRANS (@lem5258610) (@lem5258611)). Qed.
Lemma lem5258613 : term283 = False.
Proof. exact (TRANS (@lem5258607) (@lem5258612)). Qed.
Lemma lem5258614 : term280 = False.
Proof. exact (TRANS (@lem5258598) (@lem5258613)). Qed.
Lemma lem5258615 : term279 = False.
Proof. exact (TRANS (@lem5258575) (@lem5258614)). Qed.
Lemma lem5258616 : term278 = False.
Proof. exact (TRANS (@lem5258566) (@lem5258615)). Qed.
Lemma lem5258617 (a : real) (b : real) (c : real) (h1 : term200 a b c) : False.
Proof. exact (EQ_MP (@lem5258616) (@lem5258563 a b c h1)). Qed.
Lemma lem5258618 (a : real) (b : real) (c : real) (h1 : term202 a b c) : False.
Proof. exact (or_elim (@lem5257741 a b c h1) (fun h0 : term196 b a c => @lem5258179 b a c h0) (fun h0 : term200 a b c => @lem5258617 a b c h0)). Qed.
Lemma lem5258619 (a : real) (b : real) (c : real) (h1 : term213 a b c) : term213 a b c.
Proof. exact (h1). Qed.
Lemma lem5258620 (a : real) (b : real) (c : real) (h1 : term208 a b c) : term208 a b c.
Proof. exact (h1). Qed.
Lemma lem5258621 (a : real) (b : real) (c : real) (h1 : term208 a b c) : term102 a b c.
Proof. exact (proj2 (@lem5258620 a b c h1)). Qed.
Lemma lem5258622 (a : real) (b : real) (c : real) (h1 : term208 a b c) : term120 b c.
Proof. exact (proj1 (@lem5258620 a b c h1)). Qed.
Lemma lem5258623 (a : real) (b : real) (c : real) (h1 : term208 a b c) : term100 b c.
Proof. exact (proj2 (@lem5258621 a b c h1)). Qed.
Lemma lem5258626 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5258627 : term216 = term217.
Proof. exact (@lem5258626 term99 term171). Qed.
Lemma lem5258629 (x : nat) : (real_of_num x) = (term159 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5258630 : term171 = term218.
Proof. exact (@lem5258629 term165). Qed.
Lemma lem5258632 (x : nat) : (real_of_num x) = (term159 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5258633 : term99 = term160.
Proof. exact (@lem5258632 (NUMERAL 0)). Qed.
Lemma lem5258634 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5258635 : term219 = term220.
Proof. exact (MK_COMB (@lem5258634) (@lem5258633)). Qed.
Lemma lem5258636 : term217 = term221.
Proof. exact (MK_COMB (@lem5258635) (@lem5258630)). Qed.
Lemma lem5258637 : term222.
Proof. exact (@lem1980255 term99 term171 term171 term171). Qed.
Lemma lem5258639 (m : nat) (n : nat) : (term223 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5258640 : term217 = term224.
Proof. exact (@lem5258639 (NUMERAL 0) term165). Qed.
Lemma lem5258641 : term225 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5258642 (h1 : term225 = (BIT1 0)) : term224 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5258643 : (term225 = (BIT1 0)) = (term224 = True).
Proof. exact (prop_ext (fun h1 : term225 = (BIT1 0) => @lem5258642 h1) (fun h1 : term224 = True => @lem5258641)). Qed.
Lemma lem5258644 : term224 = True.
Proof. exact (EQ_MP (@lem5258643) (@lem5258641)). Qed.
Lemma lem5258645 : term217 = True.
Proof. exact (TRANS (@lem5258640) (@lem5258644)). Qed.
Lemma lem5258646 : True = term217.
Proof. exact (SYM (@lem5258645)). Qed.
Lemma lem5258647 : term217.
Proof. exact (EQ_MP (@lem5258646) (@lem0)). Qed.
Lemma lem5258648 : term226.
Proof. exact (@lem5258637 (@lem5258647)). Qed.
Lemma lem5258650 (m : nat) (n : nat) : (term223 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5258651 : term217 = term224.
Proof. exact (@lem5258650 (NUMERAL 0) term165). Qed.
Lemma lem5258652 : term225 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5258653 (h1 : term225 = (BIT1 0)) : term224 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5258654 : (term225 = (BIT1 0)) = (term224 = True).
Proof. exact (prop_ext (fun h1 : term225 = (BIT1 0) => @lem5258653 h1) (fun h1 : term224 = True => @lem5258652)). Qed.
Lemma lem5258655 : term224 = True.
Proof. exact (EQ_MP (@lem5258654) (@lem5258652)). Qed.
Lemma lem5258656 : term217 = True.
Proof. exact (TRANS (@lem5258651) (@lem5258655)). Qed.
Lemma lem5258657 : True = term217.
Proof. exact (SYM (@lem5258656)). Qed.
Lemma lem5258658 : term217.
Proof. exact (EQ_MP (@lem5258657) (@lem0)). Qed.
Lemma lem5258659 : term221 = term227.
Proof. exact (@lem5258648 (@lem5258658)). Qed.
Lemma lem5258661 (m : nat) (n : nat) : (term172 m n) = (term173 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5258662 : term174 = term175.
Proof. exact (@lem5258661 term165 term165). Qed.
Lemma lem5258663 : (term176 = (BIT1 0)) = (term177 = term165).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5258664 : term177 = term165.
Proof. exact (EQ_MP (@lem5258663) (@lem940073)). Qed.
Lemma lem5258665 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5258666 : term175 = term171.
Proof. exact (MK_COMB (@lem5258665) (@lem5258664)). Qed.
Lemma lem5258667 : term174 = term171.
Proof. exact (TRANS (@lem5258662) (@lem5258666)). Qed.
Lemma lem5258669 (x : nat) : (term228 x) = term99.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5258670 : term229 = term99.
Proof. exact (@lem5258669 term165). Qed.
Lemma lem5258671 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5258672 : term230 = term219.
Proof. exact (MK_COMB (@lem5258671) (@lem5258670)). Qed.
Lemma lem5258673 : term227 = term217.
Proof. exact (MK_COMB (@lem5258672) (@lem5258667)). Qed.
Lemma lem5258675 (m : nat) (n : nat) : (term223 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5258676 : term217 = term224.
Proof. exact (@lem5258675 (NUMERAL 0) term165). Qed.
Lemma lem5258677 : term225 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5258678 (h1 : term225 = (BIT1 0)) : term224 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5258679 : (term225 = (BIT1 0)) = (term224 = True).
Proof. exact (prop_ext (fun h1 : term225 = (BIT1 0) => @lem5258678 h1) (fun h1 : term224 = True => @lem5258677)). Qed.
Lemma lem5258680 : term224 = True.
Proof. exact (EQ_MP (@lem5258679) (@lem5258677)). Qed.
Lemma lem5258681 : term217 = True.
Proof. exact (TRANS (@lem5258676) (@lem5258680)). Qed.
Lemma lem5258682 : term227 = True.
Proof. exact (TRANS (@lem5258673) (@lem5258681)). Qed.
Lemma lem5258683 : term221 = True.
Proof. exact (TRANS (@lem5258659) (@lem5258682)). Qed.
Lemma lem5258684 : term217 = True.
Proof. exact (TRANS (@lem5258636) (@lem5258683)). Qed.
Lemma lem5258685 : term216 = True.
Proof. exact (TRANS (@lem5258627) (@lem5258684)). Qed.
Lemma lem5258686 : True = term216.
Proof. exact (SYM (@lem5258685)). Qed.
Lemma lem5258687 : term216.
Proof. exact (EQ_MP (@lem5258686) (@lem0)). Qed.
Lemma lem5258688 (a : real) (b : real) (c : real) (h1 : term208 a b c) : term231 b c.
Proof. exact (conj (@lem5258687) (@lem5258623 a b c h1)). Qed.
Lemma lem5258690 (x : real) (y : real) : term232 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5258691 (b : real) (c : real) : term233 b c.
Proof. exact (@lem5258690 term171 (term96 b c)). Qed.
Lemma lem5258692 (a : real) (b : real) (c : real) (h1 : term208 a b c) : term234 b c.
Proof. exact (@lem5258691 b c (@lem5258688 a b c h1)). Qed.
Lemma lem5258693 (b : real) (c : real) : (term235 b c) = (term96 b c).
Proof. exact (@lem1982733 (term96 b c)). Qed.
Lemma lem5258694 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5258695 (b : real) (c : real) : (term236 b c) = (term98 b c).
Proof. exact (MK_COMB (@lem5258694) (@lem5258693 b c)). Qed.
Lemma lem5258696 : term99 = term99.
Proof. exact (eq_refl term99). Qed.
Lemma lem5258697 (b : real) (c : real) : (term234 b c) = (term100 b c).
Proof. exact (MK_COMB (@lem5258695 b c) (@lem5258696)). Qed.
Lemma lem5258698 (a : real) (b : real) (c : real) (h1 : term208 a b c) : term100 b c.
Proof. exact (EQ_MP (@lem5258697 b c) (@lem5258692 a b c h1)). Qed.
Lemma lem5258700 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5258701 : term216 = term217.
Proof. exact (@lem5258700 term99 term171). Qed.
Lemma lem5258703 (x : nat) : (real_of_num x) = (term159 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5258704 : term171 = term218.
Proof. exact (@lem5258703 term165). Qed.
Lemma lem5258706 (x : nat) : (real_of_num x) = (term159 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5258707 : term99 = term160.
Proof. exact (@lem5258706 (NUMERAL 0)). Qed.
Lemma lem5258708 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5258709 : term219 = term220.
Proof. exact (MK_COMB (@lem5258708) (@lem5258707)). Qed.
Lemma lem5258710 : term217 = term221.
Proof. exact (MK_COMB (@lem5258709) (@lem5258704)). Qed.
Lemma lem5258711 : term222.
Proof. exact (@lem1980255 term99 term171 term171 term171). Qed.
Lemma lem5258713 (m : nat) (n : nat) : (term223 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5258714 : term217 = term224.
Proof. exact (@lem5258713 (NUMERAL 0) term165). Qed.
Lemma lem5258715 : term225 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5258716 (h1 : term225 = (BIT1 0)) : term224 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5258717 : (term225 = (BIT1 0)) = (term224 = True).
Proof. exact (prop_ext (fun h1 : term225 = (BIT1 0) => @lem5258716 h1) (fun h1 : term224 = True => @lem5258715)). Qed.
Lemma lem5258718 : term224 = True.
Proof. exact (EQ_MP (@lem5258717) (@lem5258715)). Qed.
Lemma lem5258719 : term217 = True.
Proof. exact (TRANS (@lem5258714) (@lem5258718)). Qed.
Lemma lem5258720 : True = term217.
Proof. exact (SYM (@lem5258719)). Qed.
Lemma lem5258721 : term217.
Proof. exact (EQ_MP (@lem5258720) (@lem0)). Qed.
Lemma lem5258722 : term226.
Proof. exact (@lem5258711 (@lem5258721)). Qed.
Lemma lem5258724 (m : nat) (n : nat) : (term223 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5258725 : term217 = term224.
Proof. exact (@lem5258724 (NUMERAL 0) term165). Qed.
Lemma lem5258726 : term225 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5258727 (h1 : term225 = (BIT1 0)) : term224 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5258728 : (term225 = (BIT1 0)) = (term224 = True).
Proof. exact (prop_ext (fun h1 : term225 = (BIT1 0) => @lem5258727 h1) (fun h1 : term224 = True => @lem5258726)). Qed.
Lemma lem5258729 : term224 = True.
Proof. exact (EQ_MP (@lem5258728) (@lem5258726)). Qed.
Lemma lem5258730 : term217 = True.
Proof. exact (TRANS (@lem5258725) (@lem5258729)). Qed.
Lemma lem5258731 : True = term217.
Proof. exact (SYM (@lem5258730)). Qed.
Lemma lem5258732 : term217.
Proof. exact (EQ_MP (@lem5258731) (@lem0)). Qed.
Lemma lem5258733 : term221 = term227.
Proof. exact (@lem5258722 (@lem5258732)). Qed.
Lemma lem5258735 (m : nat) (n : nat) : (term172 m n) = (term173 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5258736 : term174 = term175.
Proof. exact (@lem5258735 term165 term165). Qed.
Lemma lem5258737 : (term176 = (BIT1 0)) = (term177 = term165).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5258738 : term177 = term165.
Proof. exact (EQ_MP (@lem5258737) (@lem940073)). Qed.
Lemma lem5258739 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5258740 : term175 = term171.
Proof. exact (MK_COMB (@lem5258739) (@lem5258738)). Qed.
Lemma lem5258741 : term174 = term171.
Proof. exact (TRANS (@lem5258736) (@lem5258740)). Qed.
Lemma lem5258743 (x : nat) : (term228 x) = term99.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5258744 : term229 = term99.
Proof. exact (@lem5258743 term165). Qed.
Lemma lem5258745 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5258746 : term230 = term219.
Proof. exact (MK_COMB (@lem5258745) (@lem5258744)). Qed.
Lemma lem5258747 : term227 = term217.
Proof. exact (MK_COMB (@lem5258746) (@lem5258741)). Qed.
Lemma lem5258749 (m : nat) (n : nat) : (term223 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5258750 : term217 = term224.
Proof. exact (@lem5258749 (NUMERAL 0) term165). Qed.
Lemma lem5258751 : term225 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5258752 (h1 : term225 = (BIT1 0)) : term224 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5258753 : (term225 = (BIT1 0)) = (term224 = True).
Proof. exact (prop_ext (fun h1 : term225 = (BIT1 0) => @lem5258752 h1) (fun h1 : term224 = True => @lem5258751)). Qed.
Lemma lem5258754 : term224 = True.
Proof. exact (EQ_MP (@lem5258753) (@lem5258751)). Qed.
Lemma lem5258755 : term217 = True.
Proof. exact (TRANS (@lem5258750) (@lem5258754)). Qed.
Lemma lem5258756 : term227 = True.
Proof. exact (TRANS (@lem5258747) (@lem5258755)). Qed.
Lemma lem5258757 : term221 = True.
Proof. exact (TRANS (@lem5258733) (@lem5258756)). Qed.
Lemma lem5258758 : term217 = True.
Proof. exact (TRANS (@lem5258710) (@lem5258757)). Qed.
Lemma lem5258759 : term216 = True.
Proof. exact (TRANS (@lem5258701) (@lem5258758)). Qed.
Lemma lem5258760 : True = term216.
Proof. exact (SYM (@lem5258759)). Qed.
Lemma lem5258761 : term216.
Proof. exact (EQ_MP (@lem5258760) (@lem0)). Qed.
Lemma lem5258762 (a : real) (b : real) (c : real) (h1 : term208 a b c) : term237 b c.
Proof. exact (conj (@lem5258761) (@lem5258622 a b c h1)). Qed.
Lemma lem5258764 (x : real) (y : real) : term238 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem5258765 (b : real) (c : real) : term239 b c.
Proof. exact (@lem5258764 term171 (term116 b c)). Qed.
Lemma lem5258766 (a : real) (b : real) (c : real) (h1 : term208 a b c) : term240 b c.
Proof. exact (@lem5258765 b c (@lem5258762 a b c h1)). Qed.
Lemma lem5258767 (b : real) (c : real) : (term241 b c) = (term116 b c).
Proof. exact (@lem1982733 (term116 b c)). Qed.
Lemma lem5258768 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5258769 (b : real) (c : real) : (term242 b c) = (term119 b c).
Proof. exact (MK_COMB (@lem5258768) (@lem5258767 b c)). Qed.
Lemma lem5258770 : term99 = term99.
Proof. exact (eq_refl term99). Qed.
Lemma lem5258771 (b : real) (c : real) : (term240 b c) = (term120 b c).
Proof. exact (MK_COMB (@lem5258769 b c) (@lem5258770)). Qed.
Lemma lem5258772 (a : real) (b : real) (c : real) (h1 : term208 a b c) : term120 b c.
Proof. exact (EQ_MP (@lem5258771 b c) (@lem5258766 a b c h1)). Qed.
Lemma lem5258773 (a : real) (b : real) (c : real) (h1 : term208 a b c) : term243 b c.
Proof. exact (conj (@lem5258772 a b c h1) (@lem5258698 a b c h1)). Qed.
Lemma lem5258775 (x : real) (y : real) : term244 x y.
Proof. exact (proj1 (@lem1988348 x y)). Qed.
Lemma lem5258776 (b : real) (c : real) : term245 b c.
Proof. exact (@lem5258775 (term116 b c) (term96 b c)). Qed.
Lemma lem5258777 (a : real) (b : real) (c : real) (h1 : term208 a b c) : term246 b c.
Proof. exact (@lem5258776 b c (@lem5258773 a b c h1)). Qed.
Lemma lem5258778 (b : real) (c : real) : (term247 b c) = (term248 b c).
Proof. exact (@lem1982753 (term117 b) b c (term117 c)). Qed.
Lemma lem5258779 (b : real) : (term249 b) = (term250 b).
Proof. exact (@lem1982713 term163 b). Qed.
Lemma lem5258781 (x : nat) : (real_of_num x) = (term159 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5258782 : term171 = term218.
Proof. exact (@lem5258781 term165). Qed.
Lemma lem5258784 (x : nat) : (term161 x) = (term162 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5258785 : term163 = term164.
Proof. exact (@lem5258784 term165). Qed.
Lemma lem5258786 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5258787 : term251 = term252.
Proof. exact (MK_COMB (@lem5258786) (@lem5258785)). Qed.
Lemma lem5258788 : term253 = term254.
Proof. exact (MK_COMB (@lem5258787) (@lem5258782)). Qed.
Lemma lem5258789 : term255.
Proof. exact (@lem1981473 term163 term171 term171 term171 term99 term171). Qed.
Lemma lem5258791 (m : nat) (n : nat) : (term223 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5258792 : term217 = term224.
Proof. exact (@lem5258791 (NUMERAL 0) term165). Qed.
Lemma lem5258793 : term225 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5258794 (h1 : term225 = (BIT1 0)) : term224 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5258795 : (term225 = (BIT1 0)) = (term224 = True).
Proof. exact (prop_ext (fun h1 : term225 = (BIT1 0) => @lem5258794 h1) (fun h1 : term224 = True => @lem5258793)). Qed.
Lemma lem5258796 : term224 = True.
Proof. exact (EQ_MP (@lem5258795) (@lem5258793)). Qed.
Lemma lem5258797 : term217 = True.
Proof. exact (TRANS (@lem5258792) (@lem5258796)). Qed.
Lemma lem5258798 : True = term217.
Proof. exact (SYM (@lem5258797)). Qed.
Lemma lem5258799 : term217.
Proof. exact (EQ_MP (@lem5258798) (@lem0)). Qed.
Lemma lem5258800 : term256.
Proof. exact (@lem5258789 (@lem5258799)). Qed.
Lemma lem5258802 (m : nat) (n : nat) : (term223 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5258803 : term217 = term224.
Proof. exact (@lem5258802 (NUMERAL 0) term165). Qed.
Lemma lem5258804 : term225 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5258805 (h1 : term225 = (BIT1 0)) : term224 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5258806 : (term225 = (BIT1 0)) = (term224 = True).
Proof. exact (prop_ext (fun h1 : term225 = (BIT1 0) => @lem5258805 h1) (fun h1 : term224 = True => @lem5258804)). Qed.
Lemma lem5258807 : term224 = True.
Proof. exact (EQ_MP (@lem5258806) (@lem5258804)). Qed.
Lemma lem5258808 : term217 = True.
Proof. exact (TRANS (@lem5258803) (@lem5258807)). Qed.
Lemma lem5258809 : True = term217.
Proof. exact (SYM (@lem5258808)). Qed.
Lemma lem5258810 : term217.
Proof. exact (EQ_MP (@lem5258809) (@lem0)). Qed.
Lemma lem5258811 : term257.
Proof. exact (@lem5258800 (@lem5258810)). Qed.
Lemma lem5258813 (m : nat) (n : nat) : (term223 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5258814 : term217 = term224.
Proof. exact (@lem5258813 (NUMERAL 0) term165). Qed.
Lemma lem5258815 : term225 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5258816 (h1 : term225 = (BIT1 0)) : term224 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5258817 : (term225 = (BIT1 0)) = (term224 = True).
Proof. exact (prop_ext (fun h1 : term225 = (BIT1 0) => @lem5258816 h1) (fun h1 : term224 = True => @lem5258815)). Qed.
Lemma lem5258818 : term224 = True.
Proof. exact (EQ_MP (@lem5258817) (@lem5258815)). Qed.
Lemma lem5258819 : term217 = True.
Proof. exact (TRANS (@lem5258814) (@lem5258818)). Qed.
Lemma lem5258820 : True = term217.
Proof. exact (SYM (@lem5258819)). Qed.
Lemma lem5258821 : term217.
Proof. exact (EQ_MP (@lem5258820) (@lem0)). Qed.
Lemma lem5258822 : term258.
Proof. exact (@lem5258811 (@lem5258821)). Qed.
Lemma lem5258824 (m : nat) (n : nat) : (term172 m n) = (term173 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5258825 : term174 = term175.
Proof. exact (@lem5258824 term165 term165). Qed.
Lemma lem5258826 : (term176 = (BIT1 0)) = (term177 = term165).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5258827 : term177 = term165.
Proof. exact (EQ_MP (@lem5258826) (@lem940073)). Qed.
Lemma lem5258828 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5258829 : term175 = term171.
Proof. exact (MK_COMB (@lem5258828) (@lem5258827)). Qed.
Lemma lem5258830 : term174 = term171.
Proof. exact (TRANS (@lem5258825) (@lem5258829)). Qed.
Lemma lem5258832 (m : nat) (n : nat) : (term259 m n) = (term260 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5258833 : term261 = term262.
Proof. exact (@lem5258832 term165 term165). Qed.
Lemma lem5258834 : (term176 = (BIT1 0)) = (term177 = term165).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5258835 : term177 = term165.
Proof. exact (EQ_MP (@lem5258834) (@lem940073)). Qed.
Lemma lem5258836 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5258837 : term175 = term171.
Proof. exact (MK_COMB (@lem5258836) (@lem5258835)). Qed.
Lemma lem5258838 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5258839 : term262 = term163.
Proof. exact (MK_COMB (@lem5258838) (@lem5258837)). Qed.
Lemma lem5258840 : term261 = term163.
Proof. exact (TRANS (@lem5258833) (@lem5258839)). Qed.
Lemma lem5258841 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5258842 : term263 = term251.
Proof. exact (MK_COMB (@lem5258841) (@lem5258840)). Qed.
Lemma lem5258843 : term264 = term253.
Proof. exact (MK_COMB (@lem5258842) (@lem5258830)). Qed.
Lemma lem5258845 (m : nat) : (term265 m) = term99.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5258846 : term253 = term99.
Proof. exact (@lem5258845 term165). Qed.
Lemma lem5258847 : term264 = term99.
Proof. exact (TRANS (@lem5258843) (@lem5258846)). Qed.
Lemma lem5258848 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5258849 : term266 = term267.
Proof. exact (MK_COMB (@lem5258848) (@lem5258847)). Qed.
Lemma lem5258850 : term171 = term171.
Proof. exact (eq_refl term171). Qed.
Lemma lem5258851 : term268 = term229.
Proof. exact (MK_COMB (@lem5258849) (@lem5258850)). Qed.
Lemma lem5258853 (x : nat) : (term228 x) = term99.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5258854 : term229 = term99.
Proof. exact (@lem5258853 term165). Qed.
Lemma lem5258855 : term268 = term99.
Proof. exact (TRANS (@lem5258851) (@lem5258854)). Qed.
Lemma lem5258857 (m : nat) (n : nat) : (term172 m n) = (term173 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5258858 : term174 = term175.
Proof. exact (@lem5258857 term165 term165). Qed.
Lemma lem5258859 : (term176 = (BIT1 0)) = (term177 = term165).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5258860 : term177 = term165.
Proof. exact (EQ_MP (@lem5258859) (@lem940073)). Qed.
Lemma lem5258861 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5258862 : term175 = term171.
Proof. exact (MK_COMB (@lem5258861) (@lem5258860)). Qed.
Lemma lem5258863 : term174 = term171.
Proof. exact (TRANS (@lem5258858) (@lem5258862)). Qed.
Lemma lem5258864 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem5258865 : term269 = term229.
Proof. exact (MK_COMB (@lem5258864) (@lem5258863)). Qed.
Lemma lem5258867 (x : nat) : (term228 x) = term99.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5258868 : term229 = term99.
Proof. exact (@lem5258867 term165). Qed.
Lemma lem5258869 : term269 = term99.
Proof. exact (TRANS (@lem5258865) (@lem5258868)). Qed.
Lemma lem5258870 : term99 = term269.
Proof. exact (SYM (@lem5258869)). Qed.
Lemma lem5258871 : term268 = term269.
Proof. exact (TRANS (@lem5258855) (@lem5258870)). Qed.
Lemma lem5258872 : term254 = term160.
Proof. exact (@lem5258822 (@lem5258871)). Qed.
Lemma lem5258873 : term253 = term160.
Proof. exact (TRANS (@lem5258788) (@lem5258872)). Qed.
Lemma lem5258875 (x : real) : (term181 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5258876 : term160 = term99.
Proof. exact (@lem5258875 term99). Qed.
Lemma lem5258877 : term253 = term99.
Proof. exact (TRANS (@lem5258873) (@lem5258876)). Qed.
Lemma lem5258878 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5258879 : term270 = term267.
Proof. exact (MK_COMB (@lem5258878) (@lem5258877)). Qed.
Lemma lem5258880 (b : real) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem5258881 (b : real) : (term250 b) = (term271 b).
Proof. exact (MK_COMB (@lem5258879) (@lem5258880 b)). Qed.
Lemma lem5258882 (b : real) : (term249 b) = (term271 b).
Proof. exact (TRANS (@lem5258779 b) (@lem5258881 b)). Qed.
Lemma lem5258883 (b : real) : (term271 b) = term99.
Proof. exact (@lem1982719 b). Qed.
Lemma lem5258884 (b : real) : (term249 b) = term99.
Proof. exact (TRANS (@lem5258882 b) (@lem5258883 b)). Qed.
Lemma lem5258885 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5258886 (b : real) : (term272 b) = term273.
Proof. exact (MK_COMB (@lem5258885) (@lem5258884 b)). Qed.
Lemma lem5258887 (c : real) : (term274 c) = (term250 c).
Proof. exact (@lem1982715 term163 c). Qed.
Lemma lem5258889 (x : nat) : (real_of_num x) = (term159 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5258890 : term171 = term218.
Proof. exact (@lem5258889 term165). Qed.
Lemma lem5258892 (x : nat) : (term161 x) = (term162 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5258893 : term163 = term164.
Proof. exact (@lem5258892 term165). Qed.
Lemma lem5258894 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5258895 : term251 = term252.
Proof. exact (MK_COMB (@lem5258894) (@lem5258893)). Qed.
Lemma lem5258896 : term253 = term254.
Proof. exact (MK_COMB (@lem5258895) (@lem5258890)). Qed.
Lemma lem5258897 : term255.
Proof. exact (@lem1981473 term163 term171 term171 term171 term99 term171). Qed.
Lemma lem5258899 (m : nat) (n : nat) : (term223 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5258900 : term217 = term224.
Proof. exact (@lem5258899 (NUMERAL 0) term165). Qed.
Lemma lem5258901 : term225 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5258902 (h1 : term225 = (BIT1 0)) : term224 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5258903 : (term225 = (BIT1 0)) = (term224 = True).
Proof. exact (prop_ext (fun h1 : term225 = (BIT1 0) => @lem5258902 h1) (fun h1 : term224 = True => @lem5258901)). Qed.
Lemma lem5258904 : term224 = True.
Proof. exact (EQ_MP (@lem5258903) (@lem5258901)). Qed.
Lemma lem5258905 : term217 = True.
Proof. exact (TRANS (@lem5258900) (@lem5258904)). Qed.
Lemma lem5258906 : True = term217.
Proof. exact (SYM (@lem5258905)). Qed.
Lemma lem5258907 : term217.
Proof. exact (EQ_MP (@lem5258906) (@lem0)). Qed.
Lemma lem5258908 : term256.
Proof. exact (@lem5258897 (@lem5258907)). Qed.
Lemma lem5258910 (m : nat) (n : nat) : (term223 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5258911 : term217 = term224.
Proof. exact (@lem5258910 (NUMERAL 0) term165). Qed.
Lemma lem5258912 : term225 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5258913 (h1 : term225 = (BIT1 0)) : term224 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5258914 : (term225 = (BIT1 0)) = (term224 = True).
Proof. exact (prop_ext (fun h1 : term225 = (BIT1 0) => @lem5258913 h1) (fun h1 : term224 = True => @lem5258912)). Qed.
Lemma lem5258915 : term224 = True.
Proof. exact (EQ_MP (@lem5258914) (@lem5258912)). Qed.
Lemma lem5258916 : term217 = True.
Proof. exact (TRANS (@lem5258911) (@lem5258915)). Qed.
Lemma lem5258917 : True = term217.
Proof. exact (SYM (@lem5258916)). Qed.
Lemma lem5258918 : term217.
Proof. exact (EQ_MP (@lem5258917) (@lem0)). Qed.
Lemma lem5258919 : term257.
Proof. exact (@lem5258908 (@lem5258918)). Qed.
Lemma lem5258921 (m : nat) (n : nat) : (term223 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5258922 : term217 = term224.
Proof. exact (@lem5258921 (NUMERAL 0) term165). Qed.
Lemma lem5258923 : term225 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5258924 (h1 : term225 = (BIT1 0)) : term224 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5258925 : (term225 = (BIT1 0)) = (term224 = True).
Proof. exact (prop_ext (fun h1 : term225 = (BIT1 0) => @lem5258924 h1) (fun h1 : term224 = True => @lem5258923)). Qed.
Lemma lem5258926 : term224 = True.
Proof. exact (EQ_MP (@lem5258925) (@lem5258923)). Qed.
Lemma lem5258927 : term217 = True.
Proof. exact (TRANS (@lem5258922) (@lem5258926)). Qed.
Lemma lem5258928 : True = term217.
Proof. exact (SYM (@lem5258927)). Qed.
Lemma lem5258929 : term217.
Proof. exact (EQ_MP (@lem5258928) (@lem0)). Qed.
Lemma lem5258930 : term258.
Proof. exact (@lem5258919 (@lem5258929)). Qed.
Lemma lem5258932 (m : nat) (n : nat) : (term172 m n) = (term173 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5258933 : term174 = term175.
Proof. exact (@lem5258932 term165 term165). Qed.
Lemma lem5258934 : (term176 = (BIT1 0)) = (term177 = term165).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5258935 : term177 = term165.
Proof. exact (EQ_MP (@lem5258934) (@lem940073)). Qed.
Lemma lem5258936 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5258937 : term175 = term171.
Proof. exact (MK_COMB (@lem5258936) (@lem5258935)). Qed.
Lemma lem5258938 : term174 = term171.
Proof. exact (TRANS (@lem5258933) (@lem5258937)). Qed.
Lemma lem5258940 (m : nat) (n : nat) : (term259 m n) = (term260 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5258941 : term261 = term262.
Proof. exact (@lem5258940 term165 term165). Qed.
Lemma lem5258942 : (term176 = (BIT1 0)) = (term177 = term165).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5258943 : term177 = term165.
Proof. exact (EQ_MP (@lem5258942) (@lem940073)). Qed.
Lemma lem5258944 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5258945 : term175 = term171.
Proof. exact (MK_COMB (@lem5258944) (@lem5258943)). Qed.
Lemma lem5258946 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5258947 : term262 = term163.
Proof. exact (MK_COMB (@lem5258946) (@lem5258945)). Qed.
Lemma lem5258948 : term261 = term163.
Proof. exact (TRANS (@lem5258941) (@lem5258947)). Qed.
Lemma lem5258949 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5258950 : term263 = term251.
Proof. exact (MK_COMB (@lem5258949) (@lem5258948)). Qed.
Lemma lem5258951 : term264 = term253.
Proof. exact (MK_COMB (@lem5258950) (@lem5258938)). Qed.
Lemma lem5258953 (m : nat) : (term265 m) = term99.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5258954 : term253 = term99.
Proof. exact (@lem5258953 term165). Qed.
Lemma lem5258955 : term264 = term99.
Proof. exact (TRANS (@lem5258951) (@lem5258954)). Qed.
Lemma lem5258956 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5258957 : term266 = term267.
Proof. exact (MK_COMB (@lem5258956) (@lem5258955)). Qed.
Lemma lem5258958 : term171 = term171.
Proof. exact (eq_refl term171). Qed.
Lemma lem5258959 : term268 = term229.
Proof. exact (MK_COMB (@lem5258957) (@lem5258958)). Qed.
Lemma lem5258961 (x : nat) : (term228 x) = term99.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5258962 : term229 = term99.
Proof. exact (@lem5258961 term165). Qed.
Lemma lem5258963 : term268 = term99.
Proof. exact (TRANS (@lem5258959) (@lem5258962)). Qed.
Lemma lem5258965 (m : nat) (n : nat) : (term172 m n) = (term173 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5258966 : term174 = term175.
Proof. exact (@lem5258965 term165 term165). Qed.
Lemma lem5258967 : (term176 = (BIT1 0)) = (term177 = term165).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5258968 : term177 = term165.
Proof. exact (EQ_MP (@lem5258967) (@lem940073)). Qed.
Lemma lem5258969 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5258970 : term175 = term171.
Proof. exact (MK_COMB (@lem5258969) (@lem5258968)). Qed.
Lemma lem5258971 : term174 = term171.
Proof. exact (TRANS (@lem5258966) (@lem5258970)). Qed.
Lemma lem5258972 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem5258973 : term269 = term229.
Proof. exact (MK_COMB (@lem5258972) (@lem5258971)). Qed.
Lemma lem5258975 (x : nat) : (term228 x) = term99.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5258976 : term229 = term99.
Proof. exact (@lem5258975 term165). Qed.
Lemma lem5258977 : term269 = term99.
Proof. exact (TRANS (@lem5258973) (@lem5258976)). Qed.
Lemma lem5258978 : term99 = term269.
Proof. exact (SYM (@lem5258977)). Qed.
Lemma lem5258979 : term268 = term269.
Proof. exact (TRANS (@lem5258963) (@lem5258978)). Qed.
Lemma lem5258980 : term254 = term160.
Proof. exact (@lem5258930 (@lem5258979)). Qed.
Lemma lem5258981 : term253 = term160.
Proof. exact (TRANS (@lem5258896) (@lem5258980)). Qed.
Lemma lem5258983 (x : real) : (term181 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5258984 : term160 = term99.
Proof. exact (@lem5258983 term99). Qed.
Lemma lem5258985 : term253 = term99.
Proof. exact (TRANS (@lem5258981) (@lem5258984)). Qed.
Lemma lem5258986 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5258987 : term270 = term267.
Proof. exact (MK_COMB (@lem5258986) (@lem5258985)). Qed.
Lemma lem5258988 (c : real) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem5258989 (c : real) : (term250 c) = (term271 c).
Proof. exact (MK_COMB (@lem5258987) (@lem5258988 c)). Qed.
Lemma lem5258990 (c : real) : (term274 c) = (term271 c).
Proof. exact (TRANS (@lem5258887 c) (@lem5258989 c)). Qed.
Lemma lem5258991 (c : real) : (term271 c) = term99.
Proof. exact (@lem1982719 c). Qed.
Lemma lem5258992 (c : real) : (term274 c) = term99.
Proof. exact (TRANS (@lem5258990 c) (@lem5258991 c)). Qed.
Lemma lem5258993 (b : real) (c : real) : (term248 b c) = term275.
Proof. exact (MK_COMB (@lem5258886 b) (@lem5258992 c)). Qed.
Lemma lem5258994 (b : real) (c : real) : (term247 b c) = term275.
Proof. exact (TRANS (@lem5258778 b c) (@lem5258993 b c)). Qed.
Lemma lem5258995 : term275 = term99.
Proof. exact (@lem1982721 term99). Qed.
Lemma lem5258996 (b : real) (c : real) : (term247 b c) = term99.
Proof. exact (TRANS (@lem5258994 b c) (@lem5258995)). Qed.
Lemma lem5258997 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5258998 (b : real) (c : real) : (term276 b c) = term277.
Proof. exact (MK_COMB (@lem5258997) (@lem5258996 b c)). Qed.
Lemma lem5258999 : term99 = term99.
Proof. exact (eq_refl term99). Qed.
Lemma lem5259000 (b : real) (c : real) : (term246 b c) = term278.
Proof. exact (MK_COMB (@lem5258998 b c) (@lem5258999)). Qed.
Lemma lem5259001 (a : real) (b : real) (c : real) (h1 : term208 a b c) : term278.
Proof. exact (EQ_MP (@lem5259000 b c) (@lem5258777 a b c h1)). Qed.
Lemma lem5259003 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5259004 : term278 = term279.
Proof. exact (@lem5259003 term99 term99). Qed.
Lemma lem5259006 (x : nat) : (real_of_num x) = (term159 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5259007 : term99 = term160.
Proof. exact (@lem5259006 (NUMERAL 0)). Qed.
Lemma lem5259009 (x : nat) : (real_of_num x) = (term159 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5259010 : term99 = term160.
Proof. exact (@lem5259009 (NUMERAL 0)). Qed.
Lemma lem5259011 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5259012 : term219 = term220.
Proof. exact (MK_COMB (@lem5259011) (@lem5259010)). Qed.
Lemma lem5259013 : term279 = term280.
Proof. exact (MK_COMB (@lem5259012) (@lem5259007)). Qed.
Lemma lem5259014 : term281.
Proof. exact (@lem1980255 term99 term171 term99 term171). Qed.
Lemma lem5259016 (m : nat) (n : nat) : (term223 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5259017 : term217 = term224.
Proof. exact (@lem5259016 (NUMERAL 0) term165). Qed.
Lemma lem5259018 : term225 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5259019 (h1 : term225 = (BIT1 0)) : term224 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5259020 : (term225 = (BIT1 0)) = (term224 = True).
Proof. exact (prop_ext (fun h1 : term225 = (BIT1 0) => @lem5259019 h1) (fun h1 : term224 = True => @lem5259018)). Qed.
Lemma lem5259021 : term224 = True.
Proof. exact (EQ_MP (@lem5259020) (@lem5259018)). Qed.
Lemma lem5259022 : term217 = True.
Proof. exact (TRANS (@lem5259017) (@lem5259021)). Qed.
Lemma lem5259023 : True = term217.
Proof. exact (SYM (@lem5259022)). Qed.
Lemma lem5259024 : term217.
Proof. exact (EQ_MP (@lem5259023) (@lem0)). Qed.
Lemma lem5259025 : term282.
Proof. exact (@lem5259014 (@lem5259024)). Qed.
Lemma lem5259027 (m : nat) (n : nat) : (term223 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5259028 : term217 = term224.
Proof. exact (@lem5259027 (NUMERAL 0) term165). Qed.
Lemma lem5259029 : term225 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5259030 (h1 : term225 = (BIT1 0)) : term224 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5259031 : (term225 = (BIT1 0)) = (term224 = True).
Proof. exact (prop_ext (fun h1 : term225 = (BIT1 0) => @lem5259030 h1) (fun h1 : term224 = True => @lem5259029)). Qed.
Lemma lem5259032 : term224 = True.
Proof. exact (EQ_MP (@lem5259031) (@lem5259029)). Qed.
Lemma lem5259033 : term217 = True.
Proof. exact (TRANS (@lem5259028) (@lem5259032)). Qed.
Lemma lem5259034 : True = term217.
Proof. exact (SYM (@lem5259033)). Qed.
Lemma lem5259035 : term217.
Proof. exact (EQ_MP (@lem5259034) (@lem0)). Qed.
Lemma lem5259036 : term280 = term283.
Proof. exact (@lem5259025 (@lem5259035)). Qed.
Lemma lem5259038 (x : nat) : (term228 x) = term99.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5259039 : term229 = term99.
Proof. exact (@lem5259038 term165). Qed.
Lemma lem5259041 (x : nat) : (term228 x) = term99.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5259042 : term229 = term99.
Proof. exact (@lem5259041 term165). Qed.
Lemma lem5259043 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5259044 : term230 = term219.
Proof. exact (MK_COMB (@lem5259043) (@lem5259042)). Qed.
Lemma lem5259045 : term283 = term279.
Proof. exact (MK_COMB (@lem5259044) (@lem5259039)). Qed.
Lemma lem5259047 (m : nat) (n : nat) : (term223 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5259048 : term279 = term284.
Proof. exact (@lem5259047 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem5259049 : term284 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem5259050 : term279 = False.
Proof. exact (TRANS (@lem5259048) (@lem5259049)). Qed.
Lemma lem5259051 : term283 = False.
Proof. exact (TRANS (@lem5259045) (@lem5259050)). Qed.
Lemma lem5259052 : term280 = False.
Proof. exact (TRANS (@lem5259036) (@lem5259051)). Qed.
Lemma lem5259053 : term279 = False.
Proof. exact (TRANS (@lem5259013) (@lem5259052)). Qed.
Lemma lem5259054 : term278 = False.
Proof. exact (TRANS (@lem5259004) (@lem5259053)). Qed.
Lemma lem5259055 (a : real) (b : real) (c : real) (h1 : term208 a b c) : False.
Proof. exact (EQ_MP (@lem5259054) (@lem5259001 a b c h1)). Qed.
Lemma lem5259056 (a : real) (b : real) (c : real) (h1 : term210 a b c) : term210 a b c.
Proof. exact (h1). Qed.
Lemma lem5259057 (a : real) (b : real) (c : real) (h1 : term210 a b c) : term102 a b c.
Proof. exact (proj2 (@lem5259056 a b c h1)). Qed.
Lemma lem5259058 (a : real) (b : real) (c : real) (h1 : term210 a b c) : term120 a c.
Proof. exact (proj1 (@lem5259056 a b c h1)). Qed.
Lemma lem5259060 (a : real) (b : real) (c : real) (h1 : term210 a b c) : term100 a c.
Proof. exact (proj1 (@lem5259057 a b c h1)). Qed.
Lemma lem5259062 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5259063 : term216 = term217.
Proof. exact (@lem5259062 term99 term171). Qed.
Lemma lem5259065 (x : nat) : (real_of_num x) = (term159 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5259066 : term171 = term218.
Proof. exact (@lem5259065 term165). Qed.
Lemma lem5259068 (x : nat) : (real_of_num x) = (term159 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5259069 : term99 = term160.
Proof. exact (@lem5259068 (NUMERAL 0)). Qed.
Lemma lem5259070 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5259071 : term219 = term220.
Proof. exact (MK_COMB (@lem5259070) (@lem5259069)). Qed.
Lemma lem5259072 : term217 = term221.
Proof. exact (MK_COMB (@lem5259071) (@lem5259066)). Qed.
Lemma lem5259073 : term222.
Proof. exact (@lem1980255 term99 term171 term171 term171). Qed.
Lemma lem5259075 (m : nat) (n : nat) : (term223 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5259076 : term217 = term224.
Proof. exact (@lem5259075 (NUMERAL 0) term165). Qed.
Lemma lem5259077 : term225 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5259078 (h1 : term225 = (BIT1 0)) : term224 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5259079 : (term225 = (BIT1 0)) = (term224 = True).
Proof. exact (prop_ext (fun h1 : term225 = (BIT1 0) => @lem5259078 h1) (fun h1 : term224 = True => @lem5259077)). Qed.
Lemma lem5259080 : term224 = True.
Proof. exact (EQ_MP (@lem5259079) (@lem5259077)). Qed.
Lemma lem5259081 : term217 = True.
Proof. exact (TRANS (@lem5259076) (@lem5259080)). Qed.
Lemma lem5259082 : True = term217.
Proof. exact (SYM (@lem5259081)). Qed.
Lemma lem5259083 : term217.
Proof. exact (EQ_MP (@lem5259082) (@lem0)). Qed.
Lemma lem5259084 : term226.
Proof. exact (@lem5259073 (@lem5259083)). Qed.
Lemma lem5259086 (m : nat) (n : nat) : (term223 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5259087 : term217 = term224.
Proof. exact (@lem5259086 (NUMERAL 0) term165). Qed.
Lemma lem5259088 : term225 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5259089 (h1 : term225 = (BIT1 0)) : term224 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5259090 : (term225 = (BIT1 0)) = (term224 = True).
Proof. exact (prop_ext (fun h1 : term225 = (BIT1 0) => @lem5259089 h1) (fun h1 : term224 = True => @lem5259088)). Qed.
Lemma lem5259091 : term224 = True.
Proof. exact (EQ_MP (@lem5259090) (@lem5259088)). Qed.
Lemma lem5259092 : term217 = True.
Proof. exact (TRANS (@lem5259087) (@lem5259091)). Qed.
Lemma lem5259093 : True = term217.
Proof. exact (SYM (@lem5259092)). Qed.
Lemma lem5259094 : term217.
Proof. exact (EQ_MP (@lem5259093) (@lem0)). Qed.
Lemma lem5259095 : term221 = term227.
Proof. exact (@lem5259084 (@lem5259094)). Qed.
Lemma lem5259097 (m : nat) (n : nat) : (term172 m n) = (term173 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5259098 : term174 = term175.
Proof. exact (@lem5259097 term165 term165). Qed.
Lemma lem5259099 : (term176 = (BIT1 0)) = (term177 = term165).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5259100 : term177 = term165.
Proof. exact (EQ_MP (@lem5259099) (@lem940073)). Qed.
Lemma lem5259101 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5259102 : term175 = term171.
Proof. exact (MK_COMB (@lem5259101) (@lem5259100)). Qed.
Lemma lem5259103 : term174 = term171.
Proof. exact (TRANS (@lem5259098) (@lem5259102)). Qed.
Lemma lem5259105 (x : nat) : (term228 x) = term99.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5259106 : term229 = term99.
Proof. exact (@lem5259105 term165). Qed.
Lemma lem5259107 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5259108 : term230 = term219.
Proof. exact (MK_COMB (@lem5259107) (@lem5259106)). Qed.
Lemma lem5259109 : term227 = term217.
Proof. exact (MK_COMB (@lem5259108) (@lem5259103)). Qed.
Lemma lem5259111 (m : nat) (n : nat) : (term223 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5259112 : term217 = term224.
Proof. exact (@lem5259111 (NUMERAL 0) term165). Qed.
Lemma lem5259113 : term225 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5259114 (h1 : term225 = (BIT1 0)) : term224 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5259115 : (term225 = (BIT1 0)) = (term224 = True).
Proof. exact (prop_ext (fun h1 : term225 = (BIT1 0) => @lem5259114 h1) (fun h1 : term224 = True => @lem5259113)). Qed.
Lemma lem5259116 : term224 = True.
Proof. exact (EQ_MP (@lem5259115) (@lem5259113)). Qed.
Lemma lem5259117 : term217 = True.
Proof. exact (TRANS (@lem5259112) (@lem5259116)). Qed.
Lemma lem5259118 : term227 = True.
Proof. exact (TRANS (@lem5259109) (@lem5259117)). Qed.
Lemma lem5259119 : term221 = True.
Proof. exact (TRANS (@lem5259095) (@lem5259118)). Qed.
Lemma lem5259120 : term217 = True.
Proof. exact (TRANS (@lem5259072) (@lem5259119)). Qed.
Lemma lem5259121 : term216 = True.
Proof. exact (TRANS (@lem5259063) (@lem5259120)). Qed.
Lemma lem5259122 : True = term216.
Proof. exact (SYM (@lem5259121)). Qed.
Lemma lem5259123 : term216.
Proof. exact (EQ_MP (@lem5259122) (@lem0)). Qed.
Lemma lem5259124 (a : real) (b : real) (c : real) (h1 : term210 a b c) : term231 a c.
Proof. exact (conj (@lem5259123) (@lem5259060 a b c h1)). Qed.
Lemma lem5259126 (x : real) (y : real) : term232 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5259127 (a : real) (c : real) : term233 a c.
Proof. exact (@lem5259126 term171 (term96 a c)). Qed.
Lemma lem5259128 (a : real) (b : real) (c : real) (h1 : term210 a b c) : term234 a c.
Proof. exact (@lem5259127 a c (@lem5259124 a b c h1)). Qed.
Lemma lem5259129 (a : real) (c : real) : (term235 a c) = (term96 a c).
Proof. exact (@lem1982733 (term96 a c)). Qed.
Lemma lem5259130 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5259131 (a : real) (c : real) : (term236 a c) = (term98 a c).
Proof. exact (MK_COMB (@lem5259130) (@lem5259129 a c)). Qed.
Lemma lem5259132 : term99 = term99.
Proof. exact (eq_refl term99). Qed.
Lemma lem5259133 (a : real) (c : real) : (term234 a c) = (term100 a c).
Proof. exact (MK_COMB (@lem5259131 a c) (@lem5259132)). Qed.
Lemma lem5259134 (a : real) (b : real) (c : real) (h1 : term210 a b c) : term100 a c.
Proof. exact (EQ_MP (@lem5259133 a c) (@lem5259128 a b c h1)). Qed.
Lemma lem5259136 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5259137 : term216 = term217.
Proof. exact (@lem5259136 term99 term171). Qed.
Lemma lem5259139 (x : nat) : (real_of_num x) = (term159 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5259140 : term171 = term218.
Proof. exact (@lem5259139 term165). Qed.
Lemma lem5259142 (x : nat) : (real_of_num x) = (term159 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5259143 : term99 = term160.
Proof. exact (@lem5259142 (NUMERAL 0)). Qed.
Lemma lem5259144 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5259145 : term219 = term220.
Proof. exact (MK_COMB (@lem5259144) (@lem5259143)). Qed.
Lemma lem5259146 : term217 = term221.
Proof. exact (MK_COMB (@lem5259145) (@lem5259140)). Qed.
Lemma lem5259147 : term222.
Proof. exact (@lem1980255 term99 term171 term171 term171). Qed.
Lemma lem5259149 (m : nat) (n : nat) : (term223 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5259150 : term217 = term224.
Proof. exact (@lem5259149 (NUMERAL 0) term165). Qed.
Lemma lem5259151 : term225 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5259152 (h1 : term225 = (BIT1 0)) : term224 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5259153 : (term225 = (BIT1 0)) = (term224 = True).
Proof. exact (prop_ext (fun h1 : term225 = (BIT1 0) => @lem5259152 h1) (fun h1 : term224 = True => @lem5259151)). Qed.
Lemma lem5259154 : term224 = True.
Proof. exact (EQ_MP (@lem5259153) (@lem5259151)). Qed.
Lemma lem5259155 : term217 = True.
Proof. exact (TRANS (@lem5259150) (@lem5259154)). Qed.
Lemma lem5259156 : True = term217.
Proof. exact (SYM (@lem5259155)). Qed.
Lemma lem5259157 : term217.
Proof. exact (EQ_MP (@lem5259156) (@lem0)). Qed.
Lemma lem5259158 : term226.
Proof. exact (@lem5259147 (@lem5259157)). Qed.
Lemma lem5259160 (m : nat) (n : nat) : (term223 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5259161 : term217 = term224.
Proof. exact (@lem5259160 (NUMERAL 0) term165). Qed.
Lemma lem5259162 : term225 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5259163 (h1 : term225 = (BIT1 0)) : term224 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5259164 : (term225 = (BIT1 0)) = (term224 = True).
Proof. exact (prop_ext (fun h1 : term225 = (BIT1 0) => @lem5259163 h1) (fun h1 : term224 = True => @lem5259162)). Qed.
Lemma lem5259165 : term224 = True.
Proof. exact (EQ_MP (@lem5259164) (@lem5259162)). Qed.
Lemma lem5259166 : term217 = True.
Proof. exact (TRANS (@lem5259161) (@lem5259165)). Qed.
Lemma lem5259167 : True = term217.
Proof. exact (SYM (@lem5259166)). Qed.
Lemma lem5259168 : term217.
Proof. exact (EQ_MP (@lem5259167) (@lem0)). Qed.
Lemma lem5259169 : term221 = term227.
Proof. exact (@lem5259158 (@lem5259168)). Qed.
Lemma lem5259171 (m : nat) (n : nat) : (term172 m n) = (term173 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5259172 : term174 = term175.
Proof. exact (@lem5259171 term165 term165). Qed.
Lemma lem5259173 : (term176 = (BIT1 0)) = (term177 = term165).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5259174 : term177 = term165.
Proof. exact (EQ_MP (@lem5259173) (@lem940073)). Qed.
Lemma lem5259175 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5259176 : term175 = term171.
Proof. exact (MK_COMB (@lem5259175) (@lem5259174)). Qed.
Lemma lem5259177 : term174 = term171.
Proof. exact (TRANS (@lem5259172) (@lem5259176)). Qed.
Lemma lem5259179 (x : nat) : (term228 x) = term99.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5259180 : term229 = term99.
Proof. exact (@lem5259179 term165). Qed.
Lemma lem5259181 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5259182 : term230 = term219.
Proof. exact (MK_COMB (@lem5259181) (@lem5259180)). Qed.
Lemma lem5259183 : term227 = term217.
Proof. exact (MK_COMB (@lem5259182) (@lem5259177)). Qed.
Lemma lem5259185 (m : nat) (n : nat) : (term223 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5259186 : term217 = term224.
Proof. exact (@lem5259185 (NUMERAL 0) term165). Qed.
Lemma lem5259187 : term225 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5259188 (h1 : term225 = (BIT1 0)) : term224 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5259189 : (term225 = (BIT1 0)) = (term224 = True).
Proof. exact (prop_ext (fun h1 : term225 = (BIT1 0) => @lem5259188 h1) (fun h1 : term224 = True => @lem5259187)). Qed.
Lemma lem5259190 : term224 = True.
Proof. exact (EQ_MP (@lem5259189) (@lem5259187)). Qed.
Lemma lem5259191 : term217 = True.
Proof. exact (TRANS (@lem5259186) (@lem5259190)). Qed.
Lemma lem5259192 : term227 = True.
Proof. exact (TRANS (@lem5259183) (@lem5259191)). Qed.
Lemma lem5259193 : term221 = True.
Proof. exact (TRANS (@lem5259169) (@lem5259192)). Qed.
Lemma lem5259194 : term217 = True.
Proof. exact (TRANS (@lem5259146) (@lem5259193)). Qed.
Lemma lem5259195 : term216 = True.
Proof. exact (TRANS (@lem5259137) (@lem5259194)). Qed.
Lemma lem5259196 : True = term216.
Proof. exact (SYM (@lem5259195)). Qed.
Lemma lem5259197 : term216.
Proof. exact (EQ_MP (@lem5259196) (@lem0)). Qed.
Lemma lem5259198 (a : real) (b : real) (c : real) (h1 : term210 a b c) : term237 a c.
Proof. exact (conj (@lem5259197) (@lem5259058 a b c h1)). Qed.
Lemma lem5259200 (x : real) (y : real) : term238 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem5259201 (a : real) (c : real) : term239 a c.
Proof. exact (@lem5259200 term171 (term116 a c)). Qed.
Lemma lem5259202 (a : real) (b : real) (c : real) (h1 : term210 a b c) : term240 a c.
Proof. exact (@lem5259201 a c (@lem5259198 a b c h1)). Qed.
Lemma lem5259203 (a : real) (c : real) : (term241 a c) = (term116 a c).
Proof. exact (@lem1982733 (term116 a c)). Qed.
Lemma lem5259204 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5259205 (a : real) (c : real) : (term242 a c) = (term119 a c).
Proof. exact (MK_COMB (@lem5259204) (@lem5259203 a c)). Qed.
Lemma lem5259206 : term99 = term99.
Proof. exact (eq_refl term99). Qed.
Lemma lem5259207 (a : real) (c : real) : (term240 a c) = (term120 a c).
Proof. exact (MK_COMB (@lem5259205 a c) (@lem5259206)). Qed.
Lemma lem5259208 (a : real) (b : real) (c : real) (h1 : term210 a b c) : term120 a c.
Proof. exact (EQ_MP (@lem5259207 a c) (@lem5259202 a b c h1)). Qed.
Lemma lem5259209 (a : real) (b : real) (c : real) (h1 : term210 a b c) : term243 a c.
Proof. exact (conj (@lem5259208 a b c h1) (@lem5259134 a b c h1)). Qed.
Lemma lem5259211 (x : real) (y : real) : term244 x y.
Proof. exact (proj1 (@lem1988348 x y)). Qed.
Lemma lem5259212 (a : real) (c : real) : term245 a c.
Proof. exact (@lem5259211 (term116 a c) (term96 a c)). Qed.
Lemma lem5259213 (a : real) (b : real) (c : real) (h1 : term210 a b c) : term246 a c.
Proof. exact (@lem5259212 a c (@lem5259209 a b c h1)). Qed.
Lemma lem5259214 (a : real) (c : real) : (term247 a c) = (term248 a c).
Proof. exact (@lem1982753 (term117 a) a c (term117 c)). Qed.
Lemma lem5259215 (a : real) : (term249 a) = (term250 a).
Proof. exact (@lem1982713 term163 a). Qed.
Lemma lem5259217 (x : nat) : (real_of_num x) = (term159 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5259218 : term171 = term218.
Proof. exact (@lem5259217 term165). Qed.
Lemma lem5259220 (x : nat) : (term161 x) = (term162 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5259221 : term163 = term164.
Proof. exact (@lem5259220 term165). Qed.
Lemma lem5259222 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5259223 : term251 = term252.
Proof. exact (MK_COMB (@lem5259222) (@lem5259221)). Qed.
Lemma lem5259224 : term253 = term254.
Proof. exact (MK_COMB (@lem5259223) (@lem5259218)). Qed.
Lemma lem5259225 : term255.
Proof. exact (@lem1981473 term163 term171 term171 term171 term99 term171). Qed.
Lemma lem5259227 (m : nat) (n : nat) : (term223 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5259228 : term217 = term224.
Proof. exact (@lem5259227 (NUMERAL 0) term165). Qed.
Lemma lem5259229 : term225 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5259230 (h1 : term225 = (BIT1 0)) : term224 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5259231 : (term225 = (BIT1 0)) = (term224 = True).
Proof. exact (prop_ext (fun h1 : term225 = (BIT1 0) => @lem5259230 h1) (fun h1 : term224 = True => @lem5259229)). Qed.
Lemma lem5259232 : term224 = True.
Proof. exact (EQ_MP (@lem5259231) (@lem5259229)). Qed.
Lemma lem5259233 : term217 = True.
Proof. exact (TRANS (@lem5259228) (@lem5259232)). Qed.
Lemma lem5259234 : True = term217.
Proof. exact (SYM (@lem5259233)). Qed.
Lemma lem5259235 : term217.
Proof. exact (EQ_MP (@lem5259234) (@lem0)). Qed.
Lemma lem5259236 : term256.
Proof. exact (@lem5259225 (@lem5259235)). Qed.
Lemma lem5259238 (m : nat) (n : nat) : (term223 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5259239 : term217 = term224.
Proof. exact (@lem5259238 (NUMERAL 0) term165). Qed.
Lemma lem5259240 : term225 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5259241 (h1 : term225 = (BIT1 0)) : term224 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5259242 : (term225 = (BIT1 0)) = (term224 = True).
Proof. exact (prop_ext (fun h1 : term225 = (BIT1 0) => @lem5259241 h1) (fun h1 : term224 = True => @lem5259240)). Qed.
Lemma lem5259243 : term224 = True.
Proof. exact (EQ_MP (@lem5259242) (@lem5259240)). Qed.
Lemma lem5259244 : term217 = True.
Proof. exact (TRANS (@lem5259239) (@lem5259243)). Qed.
Lemma lem5259245 : True = term217.
Proof. exact (SYM (@lem5259244)). Qed.
Lemma lem5259246 : term217.
Proof. exact (EQ_MP (@lem5259245) (@lem0)). Qed.
Lemma lem5259247 : term257.
Proof. exact (@lem5259236 (@lem5259246)). Qed.
Lemma lem5259249 (m : nat) (n : nat) : (term223 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5259250 : term217 = term224.
Proof. exact (@lem5259249 (NUMERAL 0) term165). Qed.
Lemma lem5259251 : term225 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5259252 (h1 : term225 = (BIT1 0)) : term224 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5259253 : (term225 = (BIT1 0)) = (term224 = True).
Proof. exact (prop_ext (fun h1 : term225 = (BIT1 0) => @lem5259252 h1) (fun h1 : term224 = True => @lem5259251)). Qed.
Lemma lem5259254 : term224 = True.
Proof. exact (EQ_MP (@lem5259253) (@lem5259251)). Qed.
Lemma lem5259255 : term217 = True.
Proof. exact (TRANS (@lem5259250) (@lem5259254)). Qed.
Lemma lem5259256 : True = term217.
Proof. exact (SYM (@lem5259255)). Qed.
Lemma lem5259257 : term217.
Proof. exact (EQ_MP (@lem5259256) (@lem0)). Qed.
Lemma lem5259258 : term258.
Proof. exact (@lem5259247 (@lem5259257)). Qed.
Lemma lem5259260 (m : nat) (n : nat) : (term172 m n) = (term173 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5259261 : term174 = term175.
Proof. exact (@lem5259260 term165 term165). Qed.
Lemma lem5259262 : (term176 = (BIT1 0)) = (term177 = term165).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5259263 : term177 = term165.
Proof. exact (EQ_MP (@lem5259262) (@lem940073)). Qed.
Lemma lem5259264 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5259265 : term175 = term171.
Proof. exact (MK_COMB (@lem5259264) (@lem5259263)). Qed.
Lemma lem5259266 : term174 = term171.
Proof. exact (TRANS (@lem5259261) (@lem5259265)). Qed.
Lemma lem5259268 (m : nat) (n : nat) : (term259 m n) = (term260 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5259269 : term261 = term262.
Proof. exact (@lem5259268 term165 term165). Qed.
Lemma lem5259270 : (term176 = (BIT1 0)) = (term177 = term165).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5259271 : term177 = term165.
Proof. exact (EQ_MP (@lem5259270) (@lem940073)). Qed.
Lemma lem5259272 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5259273 : term175 = term171.
Proof. exact (MK_COMB (@lem5259272) (@lem5259271)). Qed.
Lemma lem5259274 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5259275 : term262 = term163.
Proof. exact (MK_COMB (@lem5259274) (@lem5259273)). Qed.
Lemma lem5259276 : term261 = term163.
Proof. exact (TRANS (@lem5259269) (@lem5259275)). Qed.
Lemma lem5259277 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5259278 : term263 = term251.
Proof. exact (MK_COMB (@lem5259277) (@lem5259276)). Qed.
Lemma lem5259279 : term264 = term253.
Proof. exact (MK_COMB (@lem5259278) (@lem5259266)). Qed.
Lemma lem5259281 (m : nat) : (term265 m) = term99.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5259282 : term253 = term99.
Proof. exact (@lem5259281 term165). Qed.
Lemma lem5259283 : term264 = term99.
Proof. exact (TRANS (@lem5259279) (@lem5259282)). Qed.
Lemma lem5259284 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5259285 : term266 = term267.
Proof. exact (MK_COMB (@lem5259284) (@lem5259283)). Qed.
Lemma lem5259286 : term171 = term171.
Proof. exact (eq_refl term171). Qed.
Lemma lem5259287 : term268 = term229.
Proof. exact (MK_COMB (@lem5259285) (@lem5259286)). Qed.
Lemma lem5259289 (x : nat) : (term228 x) = term99.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5259290 : term229 = term99.
Proof. exact (@lem5259289 term165). Qed.
Lemma lem5259291 : term268 = term99.
Proof. exact (TRANS (@lem5259287) (@lem5259290)). Qed.
Lemma lem5259293 (m : nat) (n : nat) : (term172 m n) = (term173 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5259294 : term174 = term175.
Proof. exact (@lem5259293 term165 term165). Qed.
Lemma lem5259295 : (term176 = (BIT1 0)) = (term177 = term165).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5259296 : term177 = term165.
Proof. exact (EQ_MP (@lem5259295) (@lem940073)). Qed.
Lemma lem5259297 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5259298 : term175 = term171.
Proof. exact (MK_COMB (@lem5259297) (@lem5259296)). Qed.
Lemma lem5259299 : term174 = term171.
Proof. exact (TRANS (@lem5259294) (@lem5259298)). Qed.
Lemma lem5259300 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem5259301 : term269 = term229.
Proof. exact (MK_COMB (@lem5259300) (@lem5259299)). Qed.
Lemma lem5259303 (x : nat) : (term228 x) = term99.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5259304 : term229 = term99.
Proof. exact (@lem5259303 term165). Qed.
Lemma lem5259305 : term269 = term99.
Proof. exact (TRANS (@lem5259301) (@lem5259304)). Qed.
Lemma lem5259306 : term99 = term269.
Proof. exact (SYM (@lem5259305)). Qed.
Lemma lem5259307 : term268 = term269.
Proof. exact (TRANS (@lem5259291) (@lem5259306)). Qed.
Lemma lem5259308 : term254 = term160.
Proof. exact (@lem5259258 (@lem5259307)). Qed.
Lemma lem5259309 : term253 = term160.
Proof. exact (TRANS (@lem5259224) (@lem5259308)). Qed.
Lemma lem5259311 (x : real) : (term181 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5259312 : term160 = term99.
Proof. exact (@lem5259311 term99). Qed.
Lemma lem5259313 : term253 = term99.
Proof. exact (TRANS (@lem5259309) (@lem5259312)). Qed.
Lemma lem5259314 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5259315 : term270 = term267.
Proof. exact (MK_COMB (@lem5259314) (@lem5259313)). Qed.
Lemma lem5259316 (a : real) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem5259317 (a : real) : (term250 a) = (term271 a).
Proof. exact (MK_COMB (@lem5259315) (@lem5259316 a)). Qed.
Lemma lem5259318 (a : real) : (term249 a) = (term271 a).
Proof. exact (TRANS (@lem5259215 a) (@lem5259317 a)). Qed.
Lemma lem5259319 (a : real) : (term271 a) = term99.
Proof. exact (@lem1982719 a). Qed.
Lemma lem5259320 (a : real) : (term249 a) = term99.
Proof. exact (TRANS (@lem5259318 a) (@lem5259319 a)). Qed.
Lemma lem5259321 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5259322 (a : real) : (term272 a) = term273.
Proof. exact (MK_COMB (@lem5259321) (@lem5259320 a)). Qed.
Lemma lem5259323 (c : real) : (term274 c) = (term250 c).
Proof. exact (@lem1982715 term163 c). Qed.
Lemma lem5259325 (x : nat) : (real_of_num x) = (term159 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5259326 : term171 = term218.
Proof. exact (@lem5259325 term165). Qed.
Lemma lem5259328 (x : nat) : (term161 x) = (term162 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5259329 : term163 = term164.
Proof. exact (@lem5259328 term165). Qed.
Lemma lem5259330 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5259331 : term251 = term252.
Proof. exact (MK_COMB (@lem5259330) (@lem5259329)). Qed.
Lemma lem5259332 : term253 = term254.
Proof. exact (MK_COMB (@lem5259331) (@lem5259326)). Qed.
Lemma lem5259333 : term255.
Proof. exact (@lem1981473 term163 term171 term171 term171 term99 term171). Qed.
Lemma lem5259335 (m : nat) (n : nat) : (term223 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5259336 : term217 = term224.
Proof. exact (@lem5259335 (NUMERAL 0) term165). Qed.
Lemma lem5259337 : term225 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5259338 (h1 : term225 = (BIT1 0)) : term224 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5259339 : (term225 = (BIT1 0)) = (term224 = True).
Proof. exact (prop_ext (fun h1 : term225 = (BIT1 0) => @lem5259338 h1) (fun h1 : term224 = True => @lem5259337)). Qed.
Lemma lem5259340 : term224 = True.
Proof. exact (EQ_MP (@lem5259339) (@lem5259337)). Qed.
Lemma lem5259341 : term217 = True.
Proof. exact (TRANS (@lem5259336) (@lem5259340)). Qed.
Lemma lem5259342 : True = term217.
Proof. exact (SYM (@lem5259341)). Qed.
Lemma lem5259343 : term217.
Proof. exact (EQ_MP (@lem5259342) (@lem0)). Qed.
Lemma lem5259344 : term256.
Proof. exact (@lem5259333 (@lem5259343)). Qed.
Lemma lem5259346 (m : nat) (n : nat) : (term223 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5259347 : term217 = term224.
Proof. exact (@lem5259346 (NUMERAL 0) term165). Qed.
Lemma lem5259348 : term225 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5259349 (h1 : term225 = (BIT1 0)) : term224 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5259350 : (term225 = (BIT1 0)) = (term224 = True).
Proof. exact (prop_ext (fun h1 : term225 = (BIT1 0) => @lem5259349 h1) (fun h1 : term224 = True => @lem5259348)). Qed.
Lemma lem5259351 : term224 = True.
Proof. exact (EQ_MP (@lem5259350) (@lem5259348)). Qed.
Lemma lem5259352 : term217 = True.
Proof. exact (TRANS (@lem5259347) (@lem5259351)). Qed.
Lemma lem5259353 : True = term217.
Proof. exact (SYM (@lem5259352)). Qed.
Lemma lem5259354 : term217.
Proof. exact (EQ_MP (@lem5259353) (@lem0)). Qed.
Lemma lem5259355 : term257.
Proof. exact (@lem5259344 (@lem5259354)). Qed.
Lemma lem5259357 (m : nat) (n : nat) : (term223 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5259358 : term217 = term224.
Proof. exact (@lem5259357 (NUMERAL 0) term165). Qed.
Lemma lem5259359 : term225 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5259360 (h1 : term225 = (BIT1 0)) : term224 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5259361 : (term225 = (BIT1 0)) = (term224 = True).
Proof. exact (prop_ext (fun h1 : term225 = (BIT1 0) => @lem5259360 h1) (fun h1 : term224 = True => @lem5259359)). Qed.
Lemma lem5259362 : term224 = True.
Proof. exact (EQ_MP (@lem5259361) (@lem5259359)). Qed.
Lemma lem5259363 : term217 = True.
Proof. exact (TRANS (@lem5259358) (@lem5259362)). Qed.
Lemma lem5259364 : True = term217.
Proof. exact (SYM (@lem5259363)). Qed.
Lemma lem5259365 : term217.
Proof. exact (EQ_MP (@lem5259364) (@lem0)). Qed.
Lemma lem5259366 : term258.
Proof. exact (@lem5259355 (@lem5259365)). Qed.
Lemma lem5259368 (m : nat) (n : nat) : (term172 m n) = (term173 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5259369 : term174 = term175.
Proof. exact (@lem5259368 term165 term165). Qed.
Lemma lem5259370 : (term176 = (BIT1 0)) = (term177 = term165).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5259371 : term177 = term165.
Proof. exact (EQ_MP (@lem5259370) (@lem940073)). Qed.
Lemma lem5259372 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5259373 : term175 = term171.
Proof. exact (MK_COMB (@lem5259372) (@lem5259371)). Qed.
Lemma lem5259374 : term174 = term171.
Proof. exact (TRANS (@lem5259369) (@lem5259373)). Qed.
Lemma lem5259376 (m : nat) (n : nat) : (term259 m n) = (term260 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5259377 : term261 = term262.
Proof. exact (@lem5259376 term165 term165). Qed.
Lemma lem5259378 : (term176 = (BIT1 0)) = (term177 = term165).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5259379 : term177 = term165.
Proof. exact (EQ_MP (@lem5259378) (@lem940073)). Qed.
Lemma lem5259380 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5259381 : term175 = term171.
Proof. exact (MK_COMB (@lem5259380) (@lem5259379)). Qed.
Lemma lem5259382 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5259383 : term262 = term163.
Proof. exact (MK_COMB (@lem5259382) (@lem5259381)). Qed.
Lemma lem5259384 : term261 = term163.
Proof. exact (TRANS (@lem5259377) (@lem5259383)). Qed.
Lemma lem5259385 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5259386 : term263 = term251.
Proof. exact (MK_COMB (@lem5259385) (@lem5259384)). Qed.
Lemma lem5259387 : term264 = term253.
Proof. exact (MK_COMB (@lem5259386) (@lem5259374)). Qed.
Lemma lem5259389 (m : nat) : (term265 m) = term99.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5259390 : term253 = term99.
Proof. exact (@lem5259389 term165). Qed.
Lemma lem5259391 : term264 = term99.
Proof. exact (TRANS (@lem5259387) (@lem5259390)). Qed.
Lemma lem5259392 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5259393 : term266 = term267.
Proof. exact (MK_COMB (@lem5259392) (@lem5259391)). Qed.
Lemma lem5259394 : term171 = term171.
Proof. exact (eq_refl term171). Qed.
Lemma lem5259395 : term268 = term229.
Proof. exact (MK_COMB (@lem5259393) (@lem5259394)). Qed.
Lemma lem5259397 (x : nat) : (term228 x) = term99.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5259398 : term229 = term99.
Proof. exact (@lem5259397 term165). Qed.
Lemma lem5259399 : term268 = term99.
Proof. exact (TRANS (@lem5259395) (@lem5259398)). Qed.
Lemma lem5259401 (m : nat) (n : nat) : (term172 m n) = (term173 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5259402 : term174 = term175.
Proof. exact (@lem5259401 term165 term165). Qed.
Lemma lem5259403 : (term176 = (BIT1 0)) = (term177 = term165).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5259404 : term177 = term165.
Proof. exact (EQ_MP (@lem5259403) (@lem940073)). Qed.
Lemma lem5259405 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5259406 : term175 = term171.
Proof. exact (MK_COMB (@lem5259405) (@lem5259404)). Qed.
Lemma lem5259407 : term174 = term171.
Proof. exact (TRANS (@lem5259402) (@lem5259406)). Qed.
Lemma lem5259408 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem5259409 : term269 = term229.
Proof. exact (MK_COMB (@lem5259408) (@lem5259407)). Qed.
Lemma lem5259411 (x : nat) : (term228 x) = term99.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5259412 : term229 = term99.
Proof. exact (@lem5259411 term165). Qed.
Lemma lem5259413 : term269 = term99.
Proof. exact (TRANS (@lem5259409) (@lem5259412)). Qed.
Lemma lem5259414 : term99 = term269.
Proof. exact (SYM (@lem5259413)). Qed.
Lemma lem5259415 : term268 = term269.
Proof. exact (TRANS (@lem5259399) (@lem5259414)). Qed.
Lemma lem5259416 : term254 = term160.
Proof. exact (@lem5259366 (@lem5259415)). Qed.
Lemma lem5259417 : term253 = term160.
Proof. exact (TRANS (@lem5259332) (@lem5259416)). Qed.
Lemma lem5259419 (x : real) : (term181 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5259420 : term160 = term99.
Proof. exact (@lem5259419 term99). Qed.
Lemma lem5259421 : term253 = term99.
Proof. exact (TRANS (@lem5259417) (@lem5259420)). Qed.
Lemma lem5259422 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5259423 : term270 = term267.
Proof. exact (MK_COMB (@lem5259422) (@lem5259421)). Qed.
Lemma lem5259424 (c : real) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem5259425 (c : real) : (term250 c) = (term271 c).
Proof. exact (MK_COMB (@lem5259423) (@lem5259424 c)). Qed.
Lemma lem5259426 (c : real) : (term274 c) = (term271 c).
Proof. exact (TRANS (@lem5259323 c) (@lem5259425 c)). Qed.
Lemma lem5259427 (c : real) : (term271 c) = term99.
Proof. exact (@lem1982719 c). Qed.
Lemma lem5259428 (c : real) : (term274 c) = term99.
Proof. exact (TRANS (@lem5259426 c) (@lem5259427 c)). Qed.
Lemma lem5259429 (a : real) (c : real) : (term248 a c) = term275.
Proof. exact (MK_COMB (@lem5259322 a) (@lem5259428 c)). Qed.
Lemma lem5259430 (a : real) (c : real) : (term247 a c) = term275.
Proof. exact (TRANS (@lem5259214 a c) (@lem5259429 a c)). Qed.
Lemma lem5259431 : term275 = term99.
Proof. exact (@lem1982721 term99). Qed.
Lemma lem5259432 (a : real) (c : real) : (term247 a c) = term99.
Proof. exact (TRANS (@lem5259430 a c) (@lem5259431)). Qed.
Lemma lem5259433 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5259434 (a : real) (c : real) : (term276 a c) = term277.
Proof. exact (MK_COMB (@lem5259433) (@lem5259432 a c)). Qed.
Lemma lem5259435 : term99 = term99.
Proof. exact (eq_refl term99). Qed.
Lemma lem5259436 (a : real) (c : real) : (term246 a c) = term278.
Proof. exact (MK_COMB (@lem5259434 a c) (@lem5259435)). Qed.
Lemma lem5259437 (a : real) (b : real) (c : real) (h1 : term210 a b c) : term278.
Proof. exact (EQ_MP (@lem5259436 a c) (@lem5259213 a b c h1)). Qed.
Lemma lem5259439 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5259440 : term278 = term279.
Proof. exact (@lem5259439 term99 term99). Qed.
Lemma lem5259442 (x : nat) : (real_of_num x) = (term159 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5259443 : term99 = term160.
Proof. exact (@lem5259442 (NUMERAL 0)). Qed.
Lemma lem5259445 (x : nat) : (real_of_num x) = (term159 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5259446 : term99 = term160.
Proof. exact (@lem5259445 (NUMERAL 0)). Qed.
Lemma lem5259447 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5259448 : term219 = term220.
Proof. exact (MK_COMB (@lem5259447) (@lem5259446)). Qed.
Lemma lem5259449 : term279 = term280.
Proof. exact (MK_COMB (@lem5259448) (@lem5259443)). Qed.
Lemma lem5259450 : term281.
Proof. exact (@lem1980255 term99 term171 term99 term171). Qed.
Lemma lem5259452 (m : nat) (n : nat) : (term223 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5259453 : term217 = term224.
Proof. exact (@lem5259452 (NUMERAL 0) term165). Qed.
Lemma lem5259454 : term225 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5259455 (h1 : term225 = (BIT1 0)) : term224 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5259456 : (term225 = (BIT1 0)) = (term224 = True).
Proof. exact (prop_ext (fun h1 : term225 = (BIT1 0) => @lem5259455 h1) (fun h1 : term224 = True => @lem5259454)). Qed.
Lemma lem5259457 : term224 = True.
Proof. exact (EQ_MP (@lem5259456) (@lem5259454)). Qed.
Lemma lem5259458 : term217 = True.
Proof. exact (TRANS (@lem5259453) (@lem5259457)). Qed.
Lemma lem5259459 : True = term217.
Proof. exact (SYM (@lem5259458)). Qed.
Lemma lem5259460 : term217.
Proof. exact (EQ_MP (@lem5259459) (@lem0)). Qed.
Lemma lem5259461 : term282.
Proof. exact (@lem5259450 (@lem5259460)). Qed.
Lemma lem5259463 (m : nat) (n : nat) : (term223 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5259464 : term217 = term224.
Proof. exact (@lem5259463 (NUMERAL 0) term165). Qed.
Lemma lem5259465 : term225 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5259466 (h1 : term225 = (BIT1 0)) : term224 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5259467 : (term225 = (BIT1 0)) = (term224 = True).
Proof. exact (prop_ext (fun h1 : term225 = (BIT1 0) => @lem5259466 h1) (fun h1 : term224 = True => @lem5259465)). Qed.
Lemma lem5259468 : term224 = True.
Proof. exact (EQ_MP (@lem5259467) (@lem5259465)). Qed.
Lemma lem5259469 : term217 = True.
Proof. exact (TRANS (@lem5259464) (@lem5259468)). Qed.
Lemma lem5259470 : True = term217.
Proof. exact (SYM (@lem5259469)). Qed.
Lemma lem5259471 : term217.
Proof. exact (EQ_MP (@lem5259470) (@lem0)). Qed.
Lemma lem5259472 : term280 = term283.
Proof. exact (@lem5259461 (@lem5259471)). Qed.
Lemma lem5259474 (x : nat) : (term228 x) = term99.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5259475 : term229 = term99.
Proof. exact (@lem5259474 term165). Qed.
Lemma lem5259477 (x : nat) : (term228 x) = term99.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5259478 : term229 = term99.
Proof. exact (@lem5259477 term165). Qed.
Lemma lem5259479 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5259480 : term230 = term219.
Proof. exact (MK_COMB (@lem5259479) (@lem5259478)). Qed.
Lemma lem5259481 : term283 = term279.
Proof. exact (MK_COMB (@lem5259480) (@lem5259475)). Qed.
Lemma lem5259483 (m : nat) (n : nat) : (term223 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5259484 : term279 = term284.
Proof. exact (@lem5259483 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem5259485 : term284 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem5259486 : term279 = False.
Proof. exact (TRANS (@lem5259484) (@lem5259485)). Qed.
Lemma lem5259487 : term283 = False.
Proof. exact (TRANS (@lem5259481) (@lem5259486)). Qed.
Lemma lem5259488 : term280 = False.
Proof. exact (TRANS (@lem5259472) (@lem5259487)). Qed.
Lemma lem5259489 : term279 = False.
Proof. exact (TRANS (@lem5259449) (@lem5259488)). Qed.
Lemma lem5259490 : term278 = False.
Proof. exact (TRANS (@lem5259440) (@lem5259489)). Qed.
Lemma lem5259491 (a : real) (b : real) (c : real) (h1 : term210 a b c) : False.
Proof. exact (EQ_MP (@lem5259490) (@lem5259437 a b c h1)). Qed.
Lemma lem5259492 (a : real) (b : real) (c : real) (h1 : term213 a b c) : False.
Proof. exact (or_elim (@lem5258619 a b c h1) (fun h0 : term208 a b c => @lem5259055 a b c h0) (fun h0 : term210 a b c => @lem5259491 a b c h0)). Qed.
Lemma lem5259493 (a : real) (b : real) (c : real) (h1 : term215 a b c) : False.
Proof. exact (or_elim (@lem5257740 a b c h1) (fun h0 : term202 a b c => @lem5258618 a b c h0) (fun h0 : term213 a b c => @lem5259492 a b c h0)). Qed.
Lemma lem5259494 (c : real) (a : real) (b : real) (h1 : term136 c a b) : term136 c a b.
Proof. exact (h1). Qed.
Lemma lem5259495 (c : real) (a : real) (b : real) (h1 : term136 c a b) : term215 a b c.
Proof. exact (EQ_MP (@lem5257739 a b c) (@lem5259494 c a b h1)). Qed.
Lemma lem5259496 (c : real) (a : real) (b : real) (h1 : term136 c a b) : (term215 a b c) = False.
Proof. exact (prop_ext (fun h2 : term215 a b c => @lem5259493 a b c h2) (fun h2 : False => @lem5259495 c a b h1)). Qed.
Lemma lem5259497 (c : real) (a : real) (b : real) (h1 : term136 c a b) : False.
Proof. exact (EQ_MP (@lem5259496 c a b h1) (@lem5259495 c a b h1)). Qed.
Lemma lem5259498 (c : real) (a : real) (b : real) (h1 : term94 c a b) : term94 c a b.
Proof. exact (h1). Qed.
Lemma lem5259499 (c : real) (a : real) (b : real) (h1 : term94 c a b) : term136 c a b.
Proof. exact (EQ_MP (@lem5257315 c a b) (@lem5259498 c a b h1)). Qed.
Lemma lem5259500 (c : real) (a : real) (b : real) (h1 : term94 c a b) : (term136 c a b) = False.
Proof. exact (prop_ext (fun h2 : term136 c a b => @lem5259497 c a b h2) (fun h2 : False => @lem5259499 c a b h1)). Qed.
Lemma lem5259501 (c : real) (a : real) (b : real) (h1 : term94 c a b) : False.
Proof. exact (EQ_MP (@lem5259500 c a b h1) (@lem5259499 c a b h1)). Qed.
Lemma lem5259502 (c : real) (a : real) (b : real) : term285 c a b.
Proof. exact (fun h0 : term94 c a b => @lem5259501 c a b h0). Qed.
Lemma lem5259503 (c : real) (a : real) (b : real) : term286 c a b.
Proof. exact (@lem1386578 ((term79 b c a) = (term69 c a b))). Qed.
Lemma lem5259506 (c : real) (a : real) (b : real) : (term79 b c a) = (term69 c a b).
Proof. exact (@lem5259503 c a b (@lem5259502 c a b)). Qed.
Lemma lem5259507 (a : real) (b : real) (s : real -> Prop) (c : real) (h1 : term1 s c) : (term56 b a s c) = (term72 a b s c).
Proof. exact (EQ_MP (@lem5257033 a b s c h1) (@lem5259506 c a b)). Qed.
Lemma lem5259508 (a : real) (b : real) (s : real -> Prop) (c : real) : (term56 b a s c) = (term72 a b s c).
Proof. exact (or_elim (@lem5256830 s c) (fun h0 : term1 s c => @lem5259507 a b s c h0) (fun h0 : term3 s c => @lem5257077 a b s c h0)). Qed.
Lemma lem5259509 (a : real) (b : real) (s : real -> Prop) (c : real) : (term33 b a s c) = (term65 a b s c).
Proof. exact (EQ_MP (@lem5256970 a b s c) (@lem5259508 a b s c)). Qed.
Lemma lem5259514 (a : real) (b : real) (s : real -> Prop) : term287 a b s.
Proof. exact (fun c : real => @lem5259509 a b s c). Qed.
Lemma lem5259515 (a : real) (b : real) (s : real -> Prop) : (term288 b a s) = (term289 a b s).
Proof. exact (@lem5256867 a b s (@lem5259514 a b s)). Qed.
Lemma lem5259520 (a : real) (b : real) : term290 a b.
Proof. exact (fun s : real -> Prop => @lem5259515 a b s). Qed.
Lemma lem5259525 (a : real) : term291 a.
Proof. exact (fun b : real => @lem5259520 a b). Qed.
Lemma lem5259530 : term292.
Proof. exact (fun a : real => @lem5259525 a). Qed.
