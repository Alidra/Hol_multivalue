Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import TREAL_ADD_WELLDEFR_term_abbrevs.
Require Import FORALL_PAIR_THM_spec.
Require Import HREAL_EQ_ADD_RCANCEL_spec.
Require Import thm0_spec.
Require Import thm1320004_spec.
Require Import thm1320203_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1823_spec.
Require Import treal_add_spec.
Require Import treal_eq_spec.
Lemma lem1332888 (x : hreal) : term0 x.
Proof. exact (@lem1320203 x). Qed.
Lemma lem1332889 (x : hreal) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1332890 (x : hreal) : term1 x.
Proof. exact (EQ_MP (@lem1332889 x) (@lem1332888 x)). Qed.
Lemma lem1332891 (x : hreal) (y : hreal) : term2 x y.
Proof. exact (@lem1332890 x y). Qed.
Lemma lem1332892 (x : hreal) (y : hreal) : (term2 x y) = (term3 x y).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem1332893 (x : hreal) (y : hreal) : term3 x y.
Proof. exact (EQ_MP (@lem1332892 x y) (@lem1332891 x y)). Qed.
Lemma lem1332894 (x : hreal) (y : hreal) (z : hreal) : term4 x y z.
Proof. exact (@lem1332893 x y z). Qed.
Lemma lem1332895 (x : hreal) (y : hreal) (z : hreal) : (term4 x y z) = ((term5 x y z) = (term6 x y z)).
Proof. exact (eq_refl (term4 x y z)). Qed.
Lemma lem1332897 (m : hreal) : term7 m.
Proof. exact (@lem1321459 m). Qed.
Lemma lem1332898 (m : hreal) : (term7 m) = (term8 m).
Proof. exact (eq_refl (term7 m)). Qed.
Lemma lem1332899 (m : hreal) : term8 m.
Proof. exact (EQ_MP (@lem1332898 m) (@lem1332897 m)). Qed.
Lemma lem1332900 (m : hreal) (n : hreal) : term9 m n.
Proof. exact (@lem1332899 m n). Qed.
Lemma lem1332901 (m : hreal) (n : hreal) : (term9 m n) = (term10 m n).
Proof. exact (eq_refl (term9 m n)). Qed.
Lemma lem1332902 (m : hreal) (n : hreal) : term10 m n.
Proof. exact (EQ_MP (@lem1332901 m n) (@lem1332900 m n)). Qed.
Lemma lem1332903 (m : hreal) (n : hreal) (p : hreal) : term11 m n p.
Proof. exact (@lem1332902 m n p). Qed.
Lemma lem1332904 (p : hreal) (m : hreal) (n : hreal) : (term11 m n p) = (((hreal_add m p) = (hreal_add n p)) = (m = n)).
Proof. exact (eq_refl (term11 m n p)). Qed.
Lemma lem1332906 (x : hreal) : term12 x.
Proof. exact (@lem1320004 x). Qed.
Lemma lem1332907 (x : hreal) : (term12 x) = (term13 x).
Proof. exact (eq_refl (term12 x)). Qed.
Lemma lem1332908 (x : hreal) : term13 x.
Proof. exact (EQ_MP (@lem1332907 x) (@lem1332906 x)). Qed.
Lemma lem1332909 (x : hreal) (y : hreal) : term14 x y.
Proof. exact (@lem1332908 x y). Qed.
Lemma lem1332910 (y : hreal) (x : hreal) : (term14 x y) = ((hreal_add x y) = (hreal_add y x)).
Proof. exact (eq_refl (term14 x y)). Qed.
Lemma lem1332912 (x : hreal) : term0 x.
Proof. exact (@lem1320203 x). Qed.
Lemma lem1332913 (x : hreal) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1332914 (x : hreal) : term1 x.
Proof. exact (EQ_MP (@lem1332913 x) (@lem1332912 x)). Qed.
Lemma lem1332915 (x : hreal) (y : hreal) : term2 x y.
Proof. exact (@lem1332914 x y). Qed.
Lemma lem1332916 (x : hreal) (y : hreal) : (term2 x y) = (term3 x y).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem1332917 (x : hreal) (y : hreal) : term3 x y.
Proof. exact (EQ_MP (@lem1332916 x y) (@lem1332915 x y)). Qed.
Lemma lem1332918 (x : hreal) (y : hreal) (z : hreal) : term4 x y z.
Proof. exact (@lem1332917 x y z). Qed.
Lemma lem1332919 (x : hreal) (y : hreal) (z : hreal) : (term4 x y z) = ((term5 x y z) = (term6 x y z)).
Proof. exact (eq_refl (term4 x y z)). Qed.
Lemma lem1332921 (m : hreal) : term7 m.
Proof. exact (@lem1321459 m). Qed.
Lemma lem1332922 (m : hreal) : (term7 m) = (term8 m).
Proof. exact (eq_refl (term7 m)). Qed.
Lemma lem1332923 (m : hreal) : term8 m.
Proof. exact (EQ_MP (@lem1332922 m) (@lem1332921 m)). Qed.
Lemma lem1332924 (m : hreal) (n : hreal) : term9 m n.
Proof. exact (@lem1332923 m n). Qed.
Lemma lem1332925 (m : hreal) (n : hreal) : (term9 m n) = (term10 m n).
Proof. exact (eq_refl (term9 m n)). Qed.
Lemma lem1332926 (m : hreal) (n : hreal) : term10 m n.
Proof. exact (EQ_MP (@lem1332925 m n) (@lem1332924 m n)). Qed.
Lemma lem1332927 (m : hreal) (n : hreal) (p : hreal) : term11 m n p.
Proof. exact (@lem1332926 m n p). Qed.
Lemma lem1332928 (p : hreal) (m : hreal) (n : hreal) : (term11 m n p) = (((hreal_add m p) = (hreal_add n p)) = (m = n)).
Proof. exact (eq_refl (term11 m n p)). Qed.
Lemma lem1332930 (x1 : hreal) : term15 x1.
Proof. exact (@lem1326116 x1). Qed.
Lemma lem1332931 (x1 : hreal) : (term15 x1) = (term16 x1).
Proof. exact (eq_refl (term15 x1)). Qed.
Lemma lem1332932 (x1 : hreal) : term16 x1.
Proof. exact (EQ_MP (@lem1332931 x1) (@lem1332930 x1)). Qed.
Lemma lem1332933 (x1 : hreal) (y2 : hreal) : term17 x1 y2.
Proof. exact (@lem1332932 x1 y2). Qed.
Lemma lem1332934 (x1 : hreal) (y2 : hreal) : (term17 x1 y2) = (term18 x1 y2).
Proof. exact (eq_refl (term17 x1 y2)). Qed.
Lemma lem1332935 (x1 : hreal) (y2 : hreal) : term18 x1 y2.
Proof. exact (EQ_MP (@lem1332934 x1 y2) (@lem1332933 x1 y2)). Qed.
Lemma lem1332936 (x1 : hreal) (y2 : hreal) (x2 : hreal) : term19 x1 y2 x2.
Proof. exact (@lem1332935 x1 y2 x2). Qed.
Lemma lem1332937 (x1 : hreal) (y2 : hreal) (x2 : hreal) : (term19 x1 y2 x2) = (term20 x1 y2 x2).
Proof. exact (eq_refl (term19 x1 y2 x2)). Qed.
Lemma lem1332938 (x1 : hreal) (y2 : hreal) (x2 : hreal) : term20 x1 y2 x2.
Proof. exact (EQ_MP (@lem1332937 x1 y2 x2) (@lem1332936 x1 y2 x2)). Qed.
Lemma lem1332939 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : term21 x1 y2 x2 y1.
Proof. exact (@lem1332938 x1 y2 x2 y1). Qed.
Lemma lem1332940 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : (term21 x1 y2 x2 y1) = ((term22 x1 y1 x2 y2) = ((hreal_add x1 y2) = (hreal_add x2 y1))).
Proof. exact (eq_refl (term21 x1 y2 x2 y1)). Qed.
Lemma lem1332942 (x1 : hreal) : term23 x1.
Proof. exact (@lem1323802 x1). Qed.
Lemma lem1332943 (x1 : hreal) : (term23 x1) = (term24 x1).
Proof. exact (eq_refl (term23 x1)). Qed.
Lemma lem1332944 (x1 : hreal) : term24 x1.
Proof. exact (EQ_MP (@lem1332943 x1) (@lem1332942 x1)). Qed.
Lemma lem1332945 (x1 : hreal) (x2 : hreal) : term25 x1 x2.
Proof. exact (@lem1332944 x1 x2). Qed.
Lemma lem1332946 (x1 : hreal) (x2 : hreal) : (term25 x1 x2) = (term26 x1 x2).
Proof. exact (eq_refl (term25 x1 x2)). Qed.
Lemma lem1332947 (x1 : hreal) (x2 : hreal) : term26 x1 x2.
Proof. exact (EQ_MP (@lem1332946 x1 x2) (@lem1332945 x1 x2)). Qed.
Lemma lem1332948 (x1 : hreal) (x2 : hreal) (y1 : hreal) : term27 x1 x2 y1.
Proof. exact (@lem1332947 x1 x2 y1). Qed.
Lemma lem1332949 (x1 : hreal) (x2 : hreal) (y1 : hreal) : (term27 x1 x2 y1) = (term28 x1 x2 y1).
Proof. exact (eq_refl (term27 x1 x2 y1)). Qed.
Lemma lem1332950 (x1 : hreal) (x2 : hreal) (y1 : hreal) : term28 x1 x2 y1.
Proof. exact (EQ_MP (@lem1332949 x1 x2 y1) (@lem1332948 x1 x2 y1)). Qed.
Lemma lem1332951 (x1 : hreal) (x2 : hreal) (y1 : hreal) (y2 : hreal) : term29 x1 x2 y1 y2.
Proof. exact (@lem1332950 x1 x2 y1 y2). Qed.
Lemma lem1332952 (x1 : hreal) (x2 : hreal) (y1 : hreal) (y2 : hreal) : (term29 x1 x2 y1 y2) = ((term30 x1 y1 x2 y2) = (term31 x1 x2 y1 y2)).
Proof. exact (eq_refl (term29 x1 x2 y1 y2)). Qed.
Lemma lem1332954 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : term32 _5106 _5107 P.
Proof. exact (@lem49909 _5106 _5107 P). Qed.
Lemma lem1332955 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term32 _5106 _5107 P) = ((term33 _5106 _5107 P) = (term34 _5106 _5107 P)).
Proof. exact (eq_refl (term32 _5106 _5107 P)). Qed.
Lemma lem1332962 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term33 _5106 _5107 P) = (term34 _5106 _5107 P).
Proof. exact (EQ_MP (@lem1332955 _5106 _5107 P) (@lem1332954 _5106 _5107 P)). Qed.
Lemma lem1332963 (P : type1233) : (term35 P) = (term36 P).
Proof. exact (@lem1332962 hreal hreal P). Qed.
Lemma lem1332964 : term37 = term38.
Proof. exact (@lem1332963 term39). Qed.
Lemma lem1332965 (x1 : prod hreal hreal) : (term40 x1) = (term41 x1).
Proof. exact (eq_refl (term40 x1)). Qed.
Lemma lem1332966 : term42 = term39.
Proof. exact (fun_ext (fun x1 : prod hreal hreal => @lem1332965 x1)). Qed.
Lemma lem1332967 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1332968 : term37 = term43.
Proof. exact (MK_COMB (@lem1332967) (@lem1332966)). Qed.
Lemma lem1332969 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1332970 : term44 = term45.
Proof. exact (MK_COMB (@lem1332969) (@lem1332968)). Qed.
Lemma lem1332971 (p1 : hreal) (p2 : hreal) : (term46 p1 p2) = (term47 p1 p2).
Proof. exact (eq_refl (term46 p1 p2)). Qed.
Lemma lem1332972 (p1 : hreal) : (term48 p1) = (term49 p1).
Proof. exact (fun_ext (fun p2 : hreal => @lem1332971 p1 p2)). Qed.
Lemma lem1332973 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1332974 (p1 : hreal) : (term50 p1) = (term51 p1).
Proof. exact (MK_COMB (@lem1332973) (@lem1332972 p1)). Qed.
Lemma lem1332975 : term52 = term53.
Proof. exact (fun_ext (fun p1 : hreal => @lem1332974 p1)). Qed.
Lemma lem1332976 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1332977 : term38 = term54.
Proof. exact (MK_COMB (@lem1332976) (@lem1332975)). Qed.
Lemma lem1332978 : (term37 = term38) = (term43 = term54).
Proof. exact (MK_COMB (@lem1332970) (@lem1332977)). Qed.
Lemma lem1332979 : term43 = term54.
Proof. exact (EQ_MP (@lem1332978) (@lem1332964)). Qed.
Lemma lem1332997 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term33 _5106 _5107 P) = (term34 _5106 _5107 P).
Proof. exact (EQ_MP (@lem1332955 _5106 _5107 P) (@lem1332954 _5106 _5107 P)). Qed.
Lemma lem1332998 (P : type1233) : (term35 P) = (term36 P).
Proof. exact (@lem1332997 hreal hreal P). Qed.
Lemma lem1332999 (p1 : hreal) (p2 : hreal) : (term55 p1 p2) = (term56 p1 p2).
Proof. exact (@lem1332998 (term57 p1 p2)). Qed.
Lemma lem1333000 (p1 : hreal) (p2 : hreal) (x2 : prod hreal hreal) : (term58 p1 p2 x2) = (term59 p1 p2 x2).
Proof. exact (eq_refl (term58 p1 p2 x2)). Qed.
Lemma lem1333001 (p1 : hreal) (p2 : hreal) : (term60 p1 p2) = (term57 p1 p2).
Proof. exact (fun_ext (fun x2 : prod hreal hreal => @lem1333000 p1 p2 x2)). Qed.
Lemma lem1333002 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1333003 (p1 : hreal) (p2 : hreal) : (term55 p1 p2) = (term47 p1 p2).
Proof. exact (MK_COMB (@lem1333002) (@lem1333001 p1 p2)). Qed.
Lemma lem1333004 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1333005 (p1 : hreal) (p2 : hreal) : (term61 p1 p2) = (term62 p1 p2).
Proof. exact (MK_COMB (@lem1333004) (@lem1333003 p1 p2)). Qed.
Lemma lem1333006 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) : (term63 p1 p2 p1' p2') = (term64 p1 p2 p1' p2').
Proof. exact (eq_refl (term63 p1 p2 p1' p2')). Qed.
Lemma lem1333007 (p1 : hreal) (p2 : hreal) (p1' : hreal) : (term65 p1 p2 p1') = (term66 p1 p2 p1').
Proof. exact (fun_ext (fun p2' : hreal => @lem1333006 p1 p2 p1' p2')). Qed.
Lemma lem1333008 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1333009 (p1 : hreal) (p2 : hreal) (p1' : hreal) : (term67 p1 p2 p1') = (term68 p1 p2 p1').
Proof. exact (MK_COMB (@lem1333008) (@lem1333007 p1 p2 p1')). Qed.
Lemma lem1333010 (p1 : hreal) (p2 : hreal) : (term69 p1 p2) = (term70 p1 p2).
Proof. exact (fun_ext (fun p1' : hreal => @lem1333009 p1 p2 p1')). Qed.
Lemma lem1333011 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1333012 (p1 : hreal) (p2 : hreal) : (term56 p1 p2) = (term71 p1 p2).
Proof. exact (MK_COMB (@lem1333011) (@lem1333010 p1 p2)). Qed.
Lemma lem1333013 (p1 : hreal) (p2 : hreal) : ((term55 p1 p2) = (term56 p1 p2)) = ((term47 p1 p2) = (term71 p1 p2)).
Proof. exact (MK_COMB (@lem1333005 p1 p2) (@lem1333012 p1 p2)). Qed.
Lemma lem1333014 (p1 : hreal) (p2 : hreal) : (term47 p1 p2) = (term71 p1 p2).
Proof. exact (EQ_MP (@lem1333013 p1 p2) (@lem1332999 p1 p2)). Qed.
Lemma lem1333032 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term33 _5106 _5107 P) = (term34 _5106 _5107 P).
Proof. exact (EQ_MP (@lem1332955 _5106 _5107 P) (@lem1332954 _5106 _5107 P)). Qed.
Lemma lem1333033 (P : type1233) : (term35 P) = (term36 P).
Proof. exact (@lem1333032 hreal hreal P). Qed.
Lemma lem1333034 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) : (term72 p1 p2 p1' p2') = (term73 p1 p2 p1' p2').
Proof. exact (@lem1333033 (term74 p1 p2 p1' p2')). Qed.
Lemma lem1333035 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) (y : prod hreal hreal) : (term75 p1 p2 p1' p2' y) = (term76 p1 p2 p1' p2' y).
Proof. exact (eq_refl (term75 p1 p2 p1' p2' y)). Qed.
Lemma lem1333036 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) : (term77 p1 p2 p1' p2') = (term74 p1 p2 p1' p2').
Proof. exact (fun_ext (fun y : prod hreal hreal => @lem1333035 p1 p2 p1' p2' y)). Qed.
Lemma lem1333037 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1333038 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) : (term72 p1 p2 p1' p2') = (term64 p1 p2 p1' p2').
Proof. exact (MK_COMB (@lem1333037) (@lem1333036 p1 p2 p1' p2')). Qed.
Lemma lem1333039 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1333040 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) : (term78 p1 p2 p1' p2') = (term79 p1 p2 p1' p2').
Proof. exact (MK_COMB (@lem1333039) (@lem1333038 p1 p2 p1' p2')). Qed.
Lemma lem1333041 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) (p1'' : hreal) (p2'' : hreal) : (term80 p1 p2 p1' p2' p1'' p2'') = (term81 p1 p2 p1' p2' p1'' p2'').
Proof. exact (eq_refl (term80 p1 p2 p1' p2' p1'' p2'')). Qed.
Lemma lem1333042 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) (p1'' : hreal) : (term82 p1 p2 p1' p2' p1'') = (term83 p1 p2 p1' p2' p1'').
Proof. exact (fun_ext (fun p2'' : hreal => @lem1333041 p1 p2 p1' p2' p1'' p2'')). Qed.
Lemma lem1333043 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1333044 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) (p1'' : hreal) : (term84 p1 p2 p1' p2' p1'') = (term85 p1 p2 p1' p2' p1'').
Proof. exact (MK_COMB (@lem1333043) (@lem1333042 p1 p2 p1' p2' p1'')). Qed.
Lemma lem1333045 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) : (term86 p1 p2 p1' p2') = (term87 p1 p2 p1' p2').
Proof. exact (fun_ext (fun p1'' : hreal => @lem1333044 p1 p2 p1' p2' p1'')). Qed.
Lemma lem1333046 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1333047 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) : (term73 p1 p2 p1' p2') = (term88 p1 p2 p1' p2').
Proof. exact (MK_COMB (@lem1333046) (@lem1333045 p1 p2 p1' p2')). Qed.
Lemma lem1333048 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) : ((term72 p1 p2 p1' p2') = (term73 p1 p2 p1' p2')) = ((term64 p1 p2 p1' p2') = (term88 p1 p2 p1' p2')).
Proof. exact (MK_COMB (@lem1333040 p1 p2 p1' p2') (@lem1333047 p1 p2 p1' p2')). Qed.
Lemma lem1333049 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) : (term64 p1 p2 p1' p2') = (term88 p1 p2 p1' p2').
Proof. exact (EQ_MP (@lem1333048 p1 p2 p1' p2') (@lem1333034 p1 p2 p1' p2')). Qed.
Lemma lem1333065 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : (term22 x1 y1 x2 y2) = ((hreal_add x1 y2) = (hreal_add x2 y1)).
Proof. exact (EQ_MP (@lem1332940 x1 y2 x2 y1) (@lem1332939 x1 y2 x2 y1)). Qed.
Lemma lem1333066 (p1 : hreal) (p2' : hreal) (p1' : hreal) (p2 : hreal) : (term22 p1 p2 p1' p2') = ((hreal_add p1 p2') = (hreal_add p1' p2)).
Proof. exact (@lem1333065 p1 p2' p1' p2). Qed.
Lemma lem1333069 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1333070 (p1 : hreal) (p2' : hreal) (p1' : hreal) (p2 : hreal) : (term89 p1 p2 p1' p2') = (term90 p1 p2' p1' p2).
Proof. exact (MK_COMB (@lem1333069) (@lem1333066 p1 p2' p1' p2)). Qed.
Lemma lem1333072 (x1 : hreal) (x2 : hreal) (y1 : hreal) (y2 : hreal) : (term30 x1 y1 x2 y2) = (term31 x1 x2 y1 y2).
Proof. exact (EQ_MP (@lem1332952 x1 x2 y1 y2) (@lem1332951 x1 x2 y1 y2)). Qed.
Lemma lem1333073 (p1 : hreal) (p1'' : hreal) (p2 : hreal) (p2'' : hreal) : (term30 p1 p2 p1'' p2'') = (term31 p1 p1'' p2 p2'').
Proof. exact (@lem1333072 p1 p1'' p2 p2''). Qed.
Lemma lem1333074 : treal_eq = treal_eq.
Proof. exact (eq_refl treal_eq). Qed.
Lemma lem1333075 (p1 : hreal) (p1'' : hreal) (p2 : hreal) (p2'' : hreal) : (term91 p1 p2 p1'' p2'') = (term92 p1 p1'' p2 p2'').
Proof. exact (MK_COMB (@lem1333074) (@lem1333073 p1 p1'' p2 p2'')). Qed.
Lemma lem1333077 (x1 : hreal) (x2 : hreal) (y1 : hreal) (y2 : hreal) : (term30 x1 y1 x2 y2) = (term31 x1 x2 y1 y2).
Proof. exact (EQ_MP (@lem1332952 x1 x2 y1 y2) (@lem1332951 x1 x2 y1 y2)). Qed.
Lemma lem1333078 (p1' : hreal) (p1'' : hreal) (p2' : hreal) (p2'' : hreal) : (term30 p1' p2' p1'' p2'') = (term31 p1' p1'' p2' p2'').
Proof. exact (@lem1333077 p1' p1'' p2' p2''). Qed.
Lemma lem1333079 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p1'' : hreal) (p2' : hreal) (p2'' : hreal) : (term93 p1 p2 p1' p2' p1'' p2'') = (term94 p1 p2 p1' p1'' p2' p2'').
Proof. exact (MK_COMB (@lem1333075 p1 p1'' p2 p2'') (@lem1333078 p1' p1'' p2' p2'')). Qed.
Lemma lem1333081 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : (term22 x1 y1 x2 y2) = ((hreal_add x1 y2) = (hreal_add x2 y1)).
Proof. exact (EQ_MP (@lem1332940 x1 y2 x2 y1) (@lem1332939 x1 y2 x2 y1)). Qed.
Lemma lem1333082 (p1 : hreal) (p2' : hreal) (p1' : hreal) (p1'' : hreal) (p2 : hreal) (p2'' : hreal) : (term94 p1 p2 p1' p1'' p2' p2'') = ((term95 p1 p1'' p2' p2'') = (term95 p1' p1'' p2 p2'')).
Proof. exact (@lem1333081 (hreal_add p1 p1'') (hreal_add p2' p2'') (hreal_add p1' p1'') (hreal_add p2 p2'')). Qed.
Lemma lem1333085 (p1 : hreal) (p2' : hreal) (p1' : hreal) (p1'' : hreal) (p2 : hreal) (p2'' : hreal) : (term93 p1 p2 p1' p2' p1'' p2'') = ((term95 p1 p1'' p2' p2'') = (term95 p1' p1'' p2 p2'')).
Proof. exact (TRANS (@lem1333079 p1 p2 p1' p1'' p2' p2'') (@lem1333082 p1 p2' p1' p1'' p2 p2'')). Qed.
Lemma lem1333086 (p1 : hreal) (p2' : hreal) (p1' : hreal) (p1'' : hreal) (p2 : hreal) (p2'' : hreal) : (term81 p1 p2 p1' p2' p1'' p2'') = (term96 p1 p2' p1' p1'' p2 p2'').
Proof. exact (MK_COMB (@lem1333070 p1 p2' p1' p2) (@lem1333085 p1 p2' p1' p1'' p2 p2'')). Qed.
Lemma lem1333091 (p1 : hreal) (p2' : hreal) (p1' : hreal) (p1'' : hreal) (p2 : hreal) : (term83 p1 p2 p1' p2' p1'') = (term97 p1 p2' p1' p1'' p2).
Proof. exact (fun_ext (fun p2'' : hreal => @lem1333086 p1 p2' p1' p1'' p2 p2'')). Qed.
Lemma lem1333092 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1333093 (p1 : hreal) (p2' : hreal) (p1' : hreal) (p1'' : hreal) (p2 : hreal) : (term85 p1 p2 p1' p2' p1'') = (term98 p1 p2' p1' p1'' p2).
Proof. exact (MK_COMB (@lem1333092) (@lem1333091 p1 p2' p1' p1'' p2)). Qed.
Lemma lem1333100 (p1 : hreal) (p2' : hreal) (p1' : hreal) (p2 : hreal) : (term87 p1 p2 p1' p2') = (term99 p1 p2' p1' p2).
Proof. exact (fun_ext (fun p1'' : hreal => @lem1333093 p1 p2' p1' p1'' p2)). Qed.
Lemma lem1333101 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1333102 (p1 : hreal) (p2' : hreal) (p1' : hreal) (p2 : hreal) : (term88 p1 p2 p1' p2') = (term100 p1 p2' p1' p2).
Proof. exact (MK_COMB (@lem1333101) (@lem1333100 p1 p2' p1' p2)). Qed.
Lemma lem1333109 (p1 : hreal) (p2' : hreal) (p1' : hreal) (p2 : hreal) : (term64 p1 p2 p1' p2') = (term100 p1 p2' p1' p2).
Proof. exact (TRANS (@lem1333049 p1 p2 p1' p2') (@lem1333102 p1 p2' p1' p2)). Qed.
Lemma lem1333110 (p1 : hreal) (p1' : hreal) (p2 : hreal) : (term66 p1 p2 p1') = (term101 p1 p1' p2).
Proof. exact (fun_ext (fun p2' : hreal => @lem1333109 p1 p2' p1' p2)). Qed.
Lemma lem1333111 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1333112 (p1 : hreal) (p1' : hreal) (p2 : hreal) : (term68 p1 p2 p1') = (term102 p1 p1' p2).
Proof. exact (MK_COMB (@lem1333111) (@lem1333110 p1 p1' p2)). Qed.
Lemma lem1333119 (p1 : hreal) (p2 : hreal) : (term70 p1 p2) = (term103 p1 p2).
Proof. exact (fun_ext (fun p1' : hreal => @lem1333112 p1 p1' p2)). Qed.
Lemma lem1333120 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1333121 (p1 : hreal) (p2 : hreal) : (term71 p1 p2) = (term104 p1 p2).
Proof. exact (MK_COMB (@lem1333120) (@lem1333119 p1 p2)). Qed.
Lemma lem1333128 (p1 : hreal) (p2 : hreal) : (term47 p1 p2) = (term104 p1 p2).
Proof. exact (TRANS (@lem1333014 p1 p2) (@lem1333121 p1 p2)). Qed.
Lemma lem1333129 (p1 : hreal) : (term49 p1) = (term105 p1).
Proof. exact (fun_ext (fun p2 : hreal => @lem1333128 p1 p2)). Qed.
Lemma lem1333130 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1333131 (p1 : hreal) : (term51 p1) = (term106 p1).
Proof. exact (MK_COMB (@lem1333130) (@lem1333129 p1)). Qed.
Lemma lem1333138 : term53 = term107.
Proof. exact (fun_ext (fun p1 : hreal => @lem1333131 p1)). Qed.
Lemma lem1333139 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1333140 : term54 = term108.
Proof. exact (MK_COMB (@lem1333139) (@lem1333138)). Qed.
Lemma lem1333147 : term43 = term108.
Proof. exact (TRANS (@lem1332979) (@lem1333140)). Qed.
Lemma lem1333148 : term108 = term43.
Proof. exact (SYM (@lem1333147)). Qed.
Lemma lem1333186 (x : hreal) (y : hreal) (z : hreal) : (term5 x y z) = (term6 x y z).
Proof. exact (EQ_MP (@lem1332919 x y z) (@lem1332918 x y z)). Qed.
Lemma lem1333187 (p1 : hreal) (p1'' : hreal) (p2' : hreal) (p2'' : hreal) : (term95 p1 p1'' p2' p2'') = (term109 p1 p1'' p2' p2'').
Proof. exact (@lem1333186 (hreal_add p1 p1'') p2' p2''). Qed.
Lemma lem1333188 : (@eq hreal) = (@eq hreal).
Proof. exact (eq_refl (@eq hreal)). Qed.
Lemma lem1333189 (p1 : hreal) (p1'' : hreal) (p2' : hreal) (p2'' : hreal) : (term110 p1 p1'' p2' p2'') = (term111 p1 p1'' p2' p2'').
Proof. exact (MK_COMB (@lem1333188) (@lem1333187 p1 p1'' p2' p2'')). Qed.
Lemma lem1333191 (x : hreal) (y : hreal) (z : hreal) : (term5 x y z) = (term6 x y z).
Proof. exact (EQ_MP (@lem1332919 x y z) (@lem1332918 x y z)). Qed.
Lemma lem1333192 (p1' : hreal) (p1'' : hreal) (p2 : hreal) (p2'' : hreal) : (term95 p1' p1'' p2 p2'') = (term109 p1' p1'' p2 p2'').
Proof. exact (@lem1333191 (hreal_add p1' p1'') p2 p2''). Qed.
Lemma lem1333193 (p1 : hreal) (p2' : hreal) (p1' : hreal) (p1'' : hreal) (p2 : hreal) (p2'' : hreal) : ((term95 p1 p1'' p2' p2'') = (term95 p1' p1'' p2 p2'')) = ((term109 p1 p1'' p2' p2'') = (term109 p1' p1'' p2 p2'')).
Proof. exact (MK_COMB (@lem1333189 p1 p1'' p2' p2'') (@lem1333192 p1' p1'' p2 p2'')). Qed.
Lemma lem1333195 (p : hreal) (m : hreal) (n : hreal) : ((hreal_add m p) = (hreal_add n p)) = (m = n).
Proof. exact (EQ_MP (@lem1332928 p m n) (@lem1332927 m n p)). Qed.
Lemma lem1333196 (p2'' : hreal) (p1 : hreal) (p2' : hreal) (p1' : hreal) (p1'' : hreal) (p2 : hreal) : ((term109 p1 p1'' p2' p2'') = (term109 p1' p1'' p2 p2'')) = ((term6 p1 p1'' p2') = (term6 p1' p1'' p2)).
Proof. exact (@lem1333195 p2'' (term6 p1 p1'' p2') (term6 p1' p1'' p2)). Qed.
Lemma lem1333201 (p2'' : hreal) (p1 : hreal) (p2' : hreal) (p1' : hreal) (p1'' : hreal) (p2 : hreal) : ((term95 p1 p1'' p2' p2'') = (term95 p1' p1'' p2 p2'')) = ((term6 p1 p1'' p2') = (term6 p1' p1'' p2)).
Proof. exact (TRANS (@lem1333193 p1 p2' p1' p1'' p2 p2'') (@lem1333196 p2'' p1 p2' p1' p1'' p2)). Qed.
Lemma lem1333202 (p1 : hreal) (p2' : hreal) (p1' : hreal) (p2 : hreal) : (term90 p1 p2' p1' p2) = (term90 p1 p2' p1' p2).
Proof. exact (eq_refl (term90 p1 p2' p1' p2)). Qed.
Lemma lem1333203 (p2'' : hreal) (p1 : hreal) (p2' : hreal) (p1' : hreal) (p1'' : hreal) (p2 : hreal) : (term96 p1 p2' p1' p1'' p2 p2'') = (term112 p1 p2' p1' p1'' p2).
Proof. exact (MK_COMB (@lem1333202 p1 p2' p1' p2) (@lem1333201 p2'' p1 p2' p1' p1'' p2)). Qed.
Lemma lem1333208 (p1 : hreal) (p2' : hreal) (p1' : hreal) (p1'' : hreal) (p2 : hreal) : (term97 p1 p2' p1' p1'' p2) = (term113 p1 p2' p1' p1'' p2).
Proof. exact (fun_ext (fun p2'' : hreal => @lem1333203 p2'' p1 p2' p1' p1'' p2)). Qed.
Lemma lem1333209 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1333210 (p1 : hreal) (p2' : hreal) (p1' : hreal) (p1'' : hreal) (p2 : hreal) : (term98 p1 p2' p1' p1'' p2) = (term114 p1 p2' p1' p1'' p2).
Proof. exact (MK_COMB (@lem1333209) (@lem1333208 p1 p2' p1' p1'' p2)). Qed.
Lemma lem1333212 {A : Type'} (t : Prop) : (term115 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1333213 (t : Prop) : (term116 t) = t.
Proof. exact (@lem1333212 hreal t). Qed.
Lemma lem1333214 (p1 : hreal) (p2' : hreal) (p1' : hreal) (p1'' : hreal) (p2 : hreal) : (term114 p1 p2' p1' p1'' p2) = (term112 p1 p2' p1' p1'' p2).
Proof. exact (@lem1333213 (term112 p1 p2' p1' p1'' p2)). Qed.
Lemma lem1333227 (p1 : hreal) (p2' : hreal) (p1' : hreal) (p1'' : hreal) (p2 : hreal) : (term98 p1 p2' p1' p1'' p2) = (term112 p1 p2' p1' p1'' p2).
Proof. exact (TRANS (@lem1333210 p1 p2' p1' p1'' p2) (@lem1333214 p1 p2' p1' p1'' p2)). Qed.
Lemma lem1333228 (p1 : hreal) (p2' : hreal) (p1' : hreal) (p2 : hreal) : (term99 p1 p2' p1' p2) = (term117 p1 p2' p1' p2).
Proof. exact (fun_ext (fun p1'' : hreal => @lem1333227 p1 p2' p1' p1'' p2)). Qed.
Lemma lem1333229 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1333230 (p1 : hreal) (p2' : hreal) (p1' : hreal) (p2 : hreal) : (term100 p1 p2' p1' p2) = (term118 p1 p2' p1' p2).
Proof. exact (MK_COMB (@lem1333229) (@lem1333228 p1 p2' p1' p2)). Qed.
Lemma lem1333235 (p1 : hreal) (p1' : hreal) (p2 : hreal) : (term101 p1 p1' p2) = (term119 p1 p1' p2).
Proof. exact (fun_ext (fun p2' : hreal => @lem1333230 p1 p2' p1' p2)). Qed.
Lemma lem1333236 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1333237 (p1 : hreal) (p1' : hreal) (p2 : hreal) : (term102 p1 p1' p2) = (term120 p1 p1' p2).
Proof. exact (MK_COMB (@lem1333236) (@lem1333235 p1 p1' p2)). Qed.
Lemma lem1333242 (p1 : hreal) (p2 : hreal) : (term103 p1 p2) = (term121 p1 p2).
Proof. exact (fun_ext (fun p1' : hreal => @lem1333237 p1 p1' p2)). Qed.
Lemma lem1333243 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1333244 (p1 : hreal) (p2 : hreal) : (term104 p1 p2) = (term122 p1 p2).
Proof. exact (MK_COMB (@lem1333243) (@lem1333242 p1 p2)). Qed.
Lemma lem1333249 (p1 : hreal) : (term105 p1) = (term123 p1).
Proof. exact (fun_ext (fun p2 : hreal => @lem1333244 p1 p2)). Qed.
Lemma lem1333250 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1333251 (p1 : hreal) : (term106 p1) = (term124 p1).
Proof. exact (MK_COMB (@lem1333250) (@lem1333249 p1)). Qed.
Lemma lem1333256 : term107 = term125.
Proof. exact (fun_ext (fun p1 : hreal => @lem1333251 p1)). Qed.
Lemma lem1333257 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1333258 : term108 = term126.
Proof. exact (MK_COMB (@lem1333257) (@lem1333256)). Qed.
Lemma lem1333263 : term126 = term108.
Proof. exact (SYM (@lem1333258)). Qed.
Lemma lem1333291 (y : hreal) (x : hreal) : (hreal_add x y) = (hreal_add y x).
Proof. exact (EQ_MP (@lem1332910 y x) (@lem1332909 x y)). Qed.
Lemma lem1333292 (p2' : hreal) (p1 : hreal) : (hreal_add p1 p2') = (hreal_add p2' p1).
Proof. exact (@lem1333291 p2' p1). Qed.
Lemma lem1333293 : (@eq hreal) = (@eq hreal).
Proof. exact (eq_refl (@eq hreal)). Qed.
Lemma lem1333294 (p2' : hreal) (p1 : hreal) : (term127 p1 p2') = (term127 p2' p1).
Proof. exact (MK_COMB (@lem1333293) (@lem1333292 p2' p1)). Qed.
Lemma lem1333296 (y : hreal) (x : hreal) : (hreal_add x y) = (hreal_add y x).
Proof. exact (EQ_MP (@lem1332910 y x) (@lem1332909 x y)). Qed.
Lemma lem1333297 (p2 : hreal) (p1' : hreal) : (hreal_add p1' p2) = (hreal_add p2 p1').
Proof. exact (@lem1333296 p2 p1'). Qed.
Lemma lem1333298 (p2' : hreal) (p1 : hreal) (p2 : hreal) (p1' : hreal) : ((hreal_add p1 p2') = (hreal_add p1' p2)) = ((hreal_add p2' p1) = (hreal_add p2 p1')).
Proof. exact (MK_COMB (@lem1333294 p2' p1) (@lem1333297 p2 p1')). Qed.
Lemma lem1333299 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1333300 (p2' : hreal) (p1 : hreal) (p2 : hreal) (p1' : hreal) : (term90 p1 p2' p1' p2) = (term90 p2' p1 p2 p1').
Proof. exact (MK_COMB (@lem1333299) (@lem1333298 p2' p1 p2 p1')). Qed.
Lemma lem1333304 (y : hreal) (x : hreal) : (hreal_add x y) = (hreal_add y x).
Proof. exact (EQ_MP (@lem1332910 y x) (@lem1332909 x y)). Qed.
Lemma lem1333305 (p2' : hreal) (p1 : hreal) (p1'' : hreal) : (term6 p1 p1'' p2') = (term5 p2' p1 p1'').
Proof. exact (@lem1333304 p2' (hreal_add p1 p1'')). Qed.
Lemma lem1333306 : (@eq hreal) = (@eq hreal).
Proof. exact (eq_refl (@eq hreal)). Qed.
Lemma lem1333307 (p2' : hreal) (p1 : hreal) (p1'' : hreal) : (term128 p1 p1'' p2') = (term129 p2' p1 p1'').
Proof. exact (MK_COMB (@lem1333306) (@lem1333305 p2' p1 p1'')). Qed.
Lemma lem1333309 (y : hreal) (x : hreal) : (hreal_add x y) = (hreal_add y x).
Proof. exact (EQ_MP (@lem1332910 y x) (@lem1332909 x y)). Qed.
Lemma lem1333310 (p2 : hreal) (p1' : hreal) (p1'' : hreal) : (term6 p1' p1'' p2) = (term5 p2 p1' p1'').
Proof. exact (@lem1333309 p2 (hreal_add p1' p1'')). Qed.
Lemma lem1333311 (p2' : hreal) (p1 : hreal) (p2 : hreal) (p1' : hreal) (p1'' : hreal) : ((term6 p1 p1'' p2') = (term6 p1' p1'' p2)) = ((term5 p2' p1 p1'') = (term5 p2 p1' p1'')).
Proof. exact (MK_COMB (@lem1333307 p2' p1 p1'') (@lem1333310 p2 p1' p1'')). Qed.
Lemma lem1333312 (p2' : hreal) (p1 : hreal) (p2 : hreal) (p1' : hreal) (p1'' : hreal) : (term112 p1 p2' p1' p1'' p2) = (term130 p2' p1 p2 p1' p1'').
Proof. exact (MK_COMB (@lem1333300 p2' p1 p2 p1') (@lem1333311 p2' p1 p2 p1' p1'')). Qed.
Lemma lem1333313 (p2' : hreal) (p1 : hreal) (p2 : hreal) (p1' : hreal) : (term117 p1 p2' p1' p2) = (term131 p2' p1 p2 p1').
Proof. exact (fun_ext (fun p1'' : hreal => @lem1333312 p2' p1 p2 p1' p1'')). Qed.
Lemma lem1333314 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1333315 (p2' : hreal) (p1 : hreal) (p2 : hreal) (p1' : hreal) : (term118 p1 p2' p1' p2) = (term132 p2' p1 p2 p1').
Proof. exact (MK_COMB (@lem1333314) (@lem1333313 p2' p1 p2 p1')). Qed.
Lemma lem1333316 (p1 : hreal) (p2 : hreal) (p1' : hreal) : (term119 p1 p1' p2) = (term133 p1 p2 p1').
Proof. exact (fun_ext (fun p2' : hreal => @lem1333315 p2' p1 p2 p1')). Qed.
Lemma lem1333317 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1333318 (p1 : hreal) (p2 : hreal) (p1' : hreal) : (term120 p1 p1' p2) = (term134 p1 p2 p1').
Proof. exact (MK_COMB (@lem1333317) (@lem1333316 p1 p2 p1')). Qed.
Lemma lem1333319 (p1 : hreal) (p2 : hreal) : (term121 p1 p2) = (term135 p1 p2).
Proof. exact (fun_ext (fun p1' : hreal => @lem1333318 p1 p2 p1')). Qed.
Lemma lem1333320 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1333321 (p1 : hreal) (p2 : hreal) : (term122 p1 p2) = (term136 p1 p2).
Proof. exact (MK_COMB (@lem1333320) (@lem1333319 p1 p2)). Qed.
Lemma lem1333322 (p1 : hreal) : (term123 p1) = (term137 p1).
Proof. exact (fun_ext (fun p2 : hreal => @lem1333321 p1 p2)). Qed.
Lemma lem1333323 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1333324 (p1 : hreal) : (term124 p1) = (term138 p1).
Proof. exact (MK_COMB (@lem1333323) (@lem1333322 p1)). Qed.
Lemma lem1333325 : term125 = term139.
Proof. exact (fun_ext (fun p1 : hreal => @lem1333324 p1)). Qed.
Lemma lem1333326 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1333327 : term126 = term140.
Proof. exact (MK_COMB (@lem1333326) (@lem1333325)). Qed.
Lemma lem1333328 : term140 = term126.
Proof. exact (SYM (@lem1333327)). Qed.
Lemma lem1333362 (x : hreal) (y : hreal) (z : hreal) : (term5 x y z) = (term6 x y z).
Proof. exact (EQ_MP (@lem1332895 x y z) (@lem1332894 x y z)). Qed.
Lemma lem1333363 (p2' : hreal) (p1 : hreal) (p1'' : hreal) : (term5 p2' p1 p1'') = (term6 p2' p1 p1'').
Proof. exact (@lem1333362 p2' p1 p1''). Qed.
Lemma lem1333364 : (@eq hreal) = (@eq hreal).
Proof. exact (eq_refl (@eq hreal)). Qed.
Lemma lem1333365 (p2' : hreal) (p1 : hreal) (p1'' : hreal) : (term129 p2' p1 p1'') = (term128 p2' p1 p1'').
Proof. exact (MK_COMB (@lem1333364) (@lem1333363 p2' p1 p1'')). Qed.
Lemma lem1333367 (x : hreal) (y : hreal) (z : hreal) : (term5 x y z) = (term6 x y z).
Proof. exact (EQ_MP (@lem1332895 x y z) (@lem1332894 x y z)). Qed.
Lemma lem1333368 (p2 : hreal) (p1' : hreal) (p1'' : hreal) : (term5 p2 p1' p1'') = (term6 p2 p1' p1'').
Proof. exact (@lem1333367 p2 p1' p1''). Qed.
Lemma lem1333369 (p2' : hreal) (p1 : hreal) (p2 : hreal) (p1' : hreal) (p1'' : hreal) : ((term5 p2' p1 p1'') = (term5 p2 p1' p1'')) = ((term6 p2' p1 p1'') = (term6 p2 p1' p1'')).
Proof. exact (MK_COMB (@lem1333365 p2' p1 p1'') (@lem1333368 p2 p1' p1'')). Qed.
Lemma lem1333371 (p : hreal) (m : hreal) (n : hreal) : ((hreal_add m p) = (hreal_add n p)) = (m = n).
Proof. exact (EQ_MP (@lem1332904 p m n) (@lem1332903 m n p)). Qed.
Lemma lem1333372 (p1'' : hreal) (p2' : hreal) (p1 : hreal) (p2 : hreal) (p1' : hreal) : ((term6 p2' p1 p1'') = (term6 p2 p1' p1'')) = ((hreal_add p2' p1) = (hreal_add p2 p1')).
Proof. exact (@lem1333371 p1'' (hreal_add p2' p1) (hreal_add p2 p1')). Qed.
Lemma lem1333377 (p1'' : hreal) (p2' : hreal) (p1 : hreal) (p2 : hreal) (p1' : hreal) : ((term5 p2' p1 p1'') = (term5 p2 p1' p1'')) = ((hreal_add p2' p1) = (hreal_add p2 p1')).
Proof. exact (TRANS (@lem1333369 p2' p1 p2 p1' p1'') (@lem1333372 p1'' p2' p1 p2 p1')). Qed.
Lemma lem1333378 (p2' : hreal) (p1 : hreal) (p2 : hreal) (p1' : hreal) : (term90 p2' p1 p2 p1') = (term90 p2' p1 p2 p1').
Proof. exact (eq_refl (term90 p2' p1 p2 p1')). Qed.
Lemma lem1333379 (p1'' : hreal) (p2' : hreal) (p1 : hreal) (p2 : hreal) (p1' : hreal) : (term130 p2' p1 p2 p1' p1'') = (term141 p2' p1 p2 p1').
Proof. exact (MK_COMB (@lem1333378 p2' p1 p2 p1') (@lem1333377 p1'' p2' p1 p2 p1')). Qed.
Lemma lem1333383 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem1333384 (p2' : hreal) (p1 : hreal) (p2 : hreal) (p1' : hreal) : (term141 p2' p1 p2 p1') = True.
Proof. exact (@lem1333383 ((hreal_add p2' p1) = (hreal_add p2 p1'))). Qed.
Lemma lem1333385 (p2' : hreal) (p1 : hreal) (p2 : hreal) (p1' : hreal) (p1'' : hreal) : (term130 p2' p1 p2 p1' p1'') = True.
Proof. exact (TRANS (@lem1333379 p1'' p2' p1 p2 p1') (@lem1333384 p2' p1 p2 p1')). Qed.
Lemma lem1333386 (p2' : hreal) (p1 : hreal) (p2 : hreal) (p1' : hreal) : (term131 p2' p1 p2 p1') = term142.
Proof. exact (fun_ext (fun p1'' : hreal => @lem1333385 p2' p1 p2 p1' p1'')). Qed.
Lemma lem1333387 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1333388 (p2' : hreal) (p1 : hreal) (p2 : hreal) (p1' : hreal) : (term132 p2' p1 p2 p1') = term143.
Proof. exact (MK_COMB (@lem1333387) (@lem1333386 p2' p1 p2 p1')). Qed.
Lemma lem1333390 {A : Type'} (t : Prop) : (term115 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1333391 (t : Prop) : (term116 t) = t.
Proof. exact (@lem1333390 hreal t). Qed.
Lemma lem1333392 : term143 = True.
Proof. exact (@lem1333391 True). Qed.
Lemma lem1333393 (p2' : hreal) (p1 : hreal) (p2 : hreal) (p1' : hreal) : (term132 p2' p1 p2 p1') = True.
Proof. exact (TRANS (@lem1333388 p2' p1 p2 p1') (@lem1333392)). Qed.
Lemma lem1333394 (p1 : hreal) (p2 : hreal) (p1' : hreal) : (term133 p1 p2 p1') = term142.
Proof. exact (fun_ext (fun p2' : hreal => @lem1333393 p2' p1 p2 p1')). Qed.
Lemma lem1333395 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1333396 (p1 : hreal) (p2 : hreal) (p1' : hreal) : (term134 p1 p2 p1') = term143.
Proof. exact (MK_COMB (@lem1333395) (@lem1333394 p1 p2 p1')). Qed.
Lemma lem1333398 {A : Type'} (t : Prop) : (term115 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1333399 (t : Prop) : (term116 t) = t.
Proof. exact (@lem1333398 hreal t). Qed.
Lemma lem1333400 : term143 = True.
Proof. exact (@lem1333399 True). Qed.
Lemma lem1333401 (p1 : hreal) (p2 : hreal) (p1' : hreal) : (term134 p1 p2 p1') = True.
Proof. exact (TRANS (@lem1333396 p1 p2 p1') (@lem1333400)). Qed.
Lemma lem1333402 (p1 : hreal) (p2 : hreal) : (term135 p1 p2) = term142.
Proof. exact (fun_ext (fun p1' : hreal => @lem1333401 p1 p2 p1')). Qed.
Lemma lem1333403 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1333404 (p1 : hreal) (p2 : hreal) : (term136 p1 p2) = term143.
Proof. exact (MK_COMB (@lem1333403) (@lem1333402 p1 p2)). Qed.
Lemma lem1333406 {A : Type'} (t : Prop) : (term115 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1333407 (t : Prop) : (term116 t) = t.
Proof. exact (@lem1333406 hreal t). Qed.
Lemma lem1333408 : term143 = True.
Proof. exact (@lem1333407 True). Qed.
Lemma lem1333409 (p1 : hreal) (p2 : hreal) : (term136 p1 p2) = True.
Proof. exact (TRANS (@lem1333404 p1 p2) (@lem1333408)). Qed.
Lemma lem1333410 (p1 : hreal) : (term137 p1) = term142.
Proof. exact (fun_ext (fun p2 : hreal => @lem1333409 p1 p2)). Qed.
Lemma lem1333411 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1333412 (p1 : hreal) : (term138 p1) = term143.
Proof. exact (MK_COMB (@lem1333411) (@lem1333410 p1)). Qed.
Lemma lem1333414 {A : Type'} (t : Prop) : (term115 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1333415 (t : Prop) : (term116 t) = t.
Proof. exact (@lem1333414 hreal t). Qed.
Lemma lem1333416 : term143 = True.
Proof. exact (@lem1333415 True). Qed.
Lemma lem1333417 (p1 : hreal) : (term138 p1) = True.
Proof. exact (TRANS (@lem1333412 p1) (@lem1333416)). Qed.
Lemma lem1333418 : term139 = term142.
Proof. exact (fun_ext (fun p1 : hreal => @lem1333417 p1)). Qed.
Lemma lem1333419 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1333420 : term140 = term143.
Proof. exact (MK_COMB (@lem1333419) (@lem1333418)). Qed.
Lemma lem1333422 {A : Type'} (t : Prop) : (term115 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1333423 (t : Prop) : (term116 t) = t.
Proof. exact (@lem1333422 hreal t). Qed.
Lemma lem1333424 : term143 = True.
Proof. exact (@lem1333423 True). Qed.
Lemma lem1333425 : term140 = True.
Proof. exact (TRANS (@lem1333420) (@lem1333424)). Qed.
Lemma lem1333426 : True = term140.
Proof. exact (SYM (@lem1333425)). Qed.
Lemma lem1333427 : term140.
Proof. exact (EQ_MP (@lem1333426) (@lem0)). Qed.
Lemma lem1333428 : term126.
Proof. exact (EQ_MP (@lem1333328) (@lem1333427)). Qed.
Lemma lem1333429 : term108.
Proof. exact (EQ_MP (@lem1333263) (@lem1333428)). Qed.
Lemma lem1333430 : term43.
Proof. exact (EQ_MP (@lem1333148) (@lem1333429)). Qed.
