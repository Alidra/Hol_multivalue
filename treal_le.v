Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import treal_le_term_abbrevs.
Require Import FST_spec.
Require Import SND_spec.
Lemma lem1324856 : treal_le = term0.
Proof. exact (@treal_le_def). Qed.
Lemma lem1324857 (_23652 : prod hreal hreal) : _23652 = _23652.
Proof. exact (eq_refl _23652). Qed.
Lemma lem1324858 (_23652 : prod hreal hreal) : (treal_le _23652) = (term1 _23652).
Proof. exact (MK_COMB (@lem1324856) (@lem1324857 _23652)). Qed.
Lemma lem1324859 (_23652 : prod hreal hreal) : (term1 _23652) = (term2 _23652).
Proof. exact (eq_refl (term1 _23652)). Qed.
Lemma lem1324860 (_23652 : prod hreal hreal) : (treal_le _23652) = (term2 _23652).
Proof. exact (TRANS (@lem1324858 _23652) (@lem1324859 _23652)). Qed.
Lemma lem1324861 (_23653 : prod hreal hreal) : _23653 = _23653.
Proof. exact (eq_refl _23653). Qed.
Lemma lem1324862 (_23652 : prod hreal hreal) (_23653 : prod hreal hreal) : (treal_le _23652 _23653) = (term3 _23652 _23653).
Proof. exact (MK_COMB (@lem1324860 _23652) (@lem1324861 _23653)). Qed.
Lemma lem1324863 (_23653 : prod hreal hreal) (_23652 : prod hreal hreal) : (term3 _23652 _23653) = (term4 _23653 _23652).
Proof. exact (eq_refl (term3 _23652 _23653)). Qed.
Lemma lem1324864 (_23653 : prod hreal hreal) (_23652 : prod hreal hreal) : (treal_le _23652 _23653) = (term4 _23653 _23652).
Proof. exact (TRANS (@lem1324862 _23652 _23653) (@lem1324863 _23653 _23652)). Qed.
Lemma lem1324865 (_23652 : prod hreal hreal) : term5 _23652.
Proof. exact (fun _23653 : prod hreal hreal => @lem1324864 _23653 _23652). Qed.
Lemma lem1324866 : term6.
Proof. exact (fun _23652 : prod hreal hreal => @lem1324865 _23652). Qed.
Lemma lem1324867 (_23652 : prod hreal hreal) : term7 _23652.
Proof. exact (@lem1324866 _23652). Qed.
Lemma lem1324868 (_23652 : prod hreal hreal) : (term7 _23652) = (term5 _23652).
Proof. exact (eq_refl (term7 _23652)). Qed.
Lemma lem1324869 (_23652 : prod hreal hreal) : term5 _23652.
Proof. exact (EQ_MP (@lem1324868 _23652) (@lem1324867 _23652)). Qed.
Lemma lem1324870 (_23652 : prod hreal hreal) (_23653 : prod hreal hreal) : term8 _23652 _23653.
Proof. exact (@lem1324869 _23652 _23653). Qed.
Lemma lem1324871 (_23653 : prod hreal hreal) (_23652 : prod hreal hreal) : (term8 _23652 _23653) = ((treal_le _23652 _23653) = (term4 _23653 _23652)).
Proof. exact (eq_refl (term8 _23652 _23653)). Qed.
Lemma lem1324872 (_23653 : prod hreal hreal) (_23652 : prod hreal hreal) : (treal_le _23652 _23653) = (term4 _23653 _23652).
Proof. exact (EQ_MP (@lem1324871 _23653 _23652) (@lem1324870 _23652 _23653)). Qed.
Lemma lem1324873 (x2 : hreal) (y2 : hreal) (x1 : hreal) (y1 : hreal) : (term9 x1 y1 x2 y2) = (term10 x2 y2 x1 y1).
Proof. exact (@lem1324872 (@pair hreal hreal x2 y2) (@pair hreal hreal x1 y1)). Qed.
Lemma lem1324874 {A B : Type'} (x : A) : term11 A B x.
Proof. exact (@lem48019 A B x). Qed.
Lemma lem1324875 {A B : Type'} (x : A) : (term11 A B x) = (term12 A B x).
Proof. exact (eq_refl (term11 A B x)). Qed.
Lemma lem1324876 {A B : Type'} (x : A) : term12 A B x.
Proof. exact (EQ_MP (@lem1324875 A B x) (@lem1324874 A B x)). Qed.
Lemma lem1324877 {A B : Type'} (x : A) (y : B) : term13 A B x y.
Proof. exact (@lem1324876 A B x y). Qed.
Lemma lem1324878 {A B : Type'} (x : A) (y : B) : (term13 A B x y) = ((term14 A B x y) = y).
Proof. exact (eq_refl (term13 A B x y)). Qed.
Lemma lem1324880 {A B : Type'} (x : A) : term15 A B x.
Proof. exact (@lem47827 A B x). Qed.
Lemma lem1324881 {A B : Type'} (x : A) : (term15 A B x) = (term16 A B x).
Proof. exact (eq_refl (term15 A B x)). Qed.
Lemma lem1324882 {A B : Type'} (x : A) : term16 A B x.
Proof. exact (EQ_MP (@lem1324881 A B x) (@lem1324880 A B x)). Qed.
Lemma lem1324883 {A B : Type'} (x : A) (y : B) : term17 A B x y.
Proof. exact (@lem1324882 A B x y). Qed.
Lemma lem1324884 {A B : Type'} (y : B) (x : A) : (term17 A B x y) = ((term18 A B x y) = x).
Proof. exact (eq_refl (term17 A B x y)). Qed.
Lemma lem1324887 {A B : Type'} (y : B) (x : A) : (term18 A B x y) = x.
Proof. exact (EQ_MP (@lem1324884 A B y x) (@lem1324883 A B x y)). Qed.
Lemma lem1324888 (y : hreal) (x : hreal) : (term19 x y) = x.
Proof. exact (@lem1324887 hreal hreal y x). Qed.
Lemma lem1324889 (y1 : hreal) (x1 : hreal) : (term19 x1 y1) = x1.
Proof. exact (@lem1324888 y1 x1). Qed.
Lemma lem1324890 (x1 : hreal) (y1 : hreal) : x1 = (term19 x1 y1).
Proof. exact (SYM (@lem1324889 y1 x1)). Qed.
Lemma lem1324892 {A B : Type'} (x : A) (y : B) : (term14 A B x y) = y.
Proof. exact (EQ_MP (@lem1324878 A B x y) (@lem1324877 A B x y)). Qed.
Lemma lem1324893 (x : hreal) (y : hreal) : (term20 x y) = y.
Proof. exact (@lem1324892 hreal hreal x y). Qed.
Lemma lem1324894 (x1 : hreal) (y1 : hreal) : (term20 x1 y1) = y1.
Proof. exact (@lem1324893 x1 y1). Qed.
Lemma lem1324895 (x1 : hreal) (y1 : hreal) : y1 = (term20 x1 y1).
Proof. exact (SYM (@lem1324894 x1 y1)). Qed.
Lemma lem1324897 {A B : Type'} (y : B) (x : A) : (term18 A B x y) = x.
Proof. exact (EQ_MP (@lem1324884 A B y x) (@lem1324883 A B x y)). Qed.
Lemma lem1324898 (y : hreal) (x : hreal) : (term19 x y) = x.
Proof. exact (@lem1324897 hreal hreal y x). Qed.
Lemma lem1324899 (y2 : hreal) (x2 : hreal) : (term19 x2 y2) = x2.
Proof. exact (@lem1324898 y2 x2). Qed.
Lemma lem1324900 (x2 : hreal) (y2 : hreal) : x2 = (term19 x2 y2).
Proof. exact (SYM (@lem1324899 y2 x2)). Qed.
Lemma lem1324902 {A B : Type'} (x : A) (y : B) : (term14 A B x y) = y.
Proof. exact (EQ_MP (@lem1324878 A B x y) (@lem1324877 A B x y)). Qed.
Lemma lem1324903 (x : hreal) (y : hreal) : (term20 x y) = y.
Proof. exact (@lem1324902 hreal hreal x y). Qed.
Lemma lem1324904 (x2 : hreal) (y2 : hreal) : (term20 x2 y2) = y2.
Proof. exact (@lem1324903 x2 y2). Qed.
Lemma lem1324905 (x2 : hreal) (y2 : hreal) : y2 = (term20 x2 y2).
Proof. exact (SYM (@lem1324904 x2 y2)). Qed.
Lemma lem1324906 : term21 = term21.
Proof. exact (eq_refl term21). Qed.
Lemma lem1324907 (x1 : hreal) (y1 : hreal) : (term22 x1) = (term23 x1 y1).
Proof. exact (MK_COMB (@lem1324906) (@lem1324890 x1 y1)). Qed.
Lemma lem1324908 (x1 : hreal) (y1 : hreal) : (term23 x1 y1) = (term24 x1 y1).
Proof. exact (eq_refl (term23 x1 y1)). Qed.
Lemma lem1324909 (x1 : hreal) : (term25 x1) = (term25 x1).
Proof. exact (eq_refl (term25 x1)). Qed.
Lemma lem1324910 (x1 : hreal) (y1 : hreal) : ((term22 x1) = (term23 x1 y1)) = ((term22 x1) = (term24 x1 y1)).
Proof. exact (MK_COMB (@lem1324909 x1) (@lem1324908 x1 y1)). Qed.
Lemma lem1324911 (x1 : hreal) : (term22 x1) = (term26 x1).
Proof. exact (eq_refl (term22 x1)). Qed.
Lemma lem1324912 : (@eq (hreal -> hreal -> hreal -> Prop)) = (@eq (hreal -> hreal -> hreal -> Prop)).
Proof. exact (eq_refl (@eq (hreal -> hreal -> hreal -> Prop))). Qed.
Lemma lem1324913 (x1 : hreal) : (term25 x1) = (term27 x1).
Proof. exact (MK_COMB (@lem1324912) (@lem1324911 x1)). Qed.
Lemma lem1324914 (x1 : hreal) (y1 : hreal) : (term24 x1 y1) = (term24 x1 y1).
Proof. exact (eq_refl (term24 x1 y1)). Qed.
Lemma lem1324915 (x1 : hreal) (y1 : hreal) : ((term22 x1) = (term24 x1 y1)) = ((term26 x1) = (term24 x1 y1)).
Proof. exact (MK_COMB (@lem1324913 x1) (@lem1324914 x1 y1)). Qed.
Lemma lem1324916 (x1 : hreal) (y1 : hreal) : ((term22 x1) = (term23 x1 y1)) = ((term26 x1) = (term24 x1 y1)).
Proof. exact (TRANS (@lem1324910 x1 y1) (@lem1324915 x1 y1)). Qed.
Lemma lem1324917 (x1 : hreal) (y1 : hreal) : (term26 x1) = (term24 x1 y1).
Proof. exact (EQ_MP (@lem1324916 x1 y1) (@lem1324907 x1 y1)). Qed.
Lemma lem1324918 (x1 : hreal) (y1 : hreal) : (term28 x1 y1) = (term29 x1 y1).
Proof. exact (MK_COMB (@lem1324917 x1 y1) (@lem1324895 x1 y1)). Qed.
Lemma lem1324919 (x1 : hreal) (y1 : hreal) : (term29 x1 y1) = (term30 x1 y1).
Proof. exact (eq_refl (term29 x1 y1)). Qed.
Lemma lem1324920 (x1 : hreal) (y1 : hreal) : (term31 x1 y1) = (term31 x1 y1).
Proof. exact (eq_refl (term31 x1 y1)). Qed.
Lemma lem1324921 (x1 : hreal) (y1 : hreal) : ((term28 x1 y1) = (term29 x1 y1)) = ((term28 x1 y1) = (term30 x1 y1)).
Proof. exact (MK_COMB (@lem1324920 x1 y1) (@lem1324919 x1 y1)). Qed.
Lemma lem1324922 (x1 : hreal) (y1 : hreal) : (term28 x1 y1) = (term32 x1 y1).
Proof. exact (eq_refl (term28 x1 y1)). Qed.
Lemma lem1324923 : (@eq (hreal -> hreal -> Prop)) = (@eq (hreal -> hreal -> Prop)).
Proof. exact (eq_refl (@eq (hreal -> hreal -> Prop))). Qed.
Lemma lem1324924 (x1 : hreal) (y1 : hreal) : (term31 x1 y1) = (term33 x1 y1).
Proof. exact (MK_COMB (@lem1324923) (@lem1324922 x1 y1)). Qed.
Lemma lem1324925 (x1 : hreal) (y1 : hreal) : (term30 x1 y1) = (term30 x1 y1).
Proof. exact (eq_refl (term30 x1 y1)). Qed.
Lemma lem1324926 (x1 : hreal) (y1 : hreal) : ((term28 x1 y1) = (term30 x1 y1)) = ((term32 x1 y1) = (term30 x1 y1)).
Proof. exact (MK_COMB (@lem1324924 x1 y1) (@lem1324925 x1 y1)). Qed.
Lemma lem1324927 (x1 : hreal) (y1 : hreal) : ((term28 x1 y1) = (term29 x1 y1)) = ((term32 x1 y1) = (term30 x1 y1)).
Proof. exact (TRANS (@lem1324921 x1 y1) (@lem1324926 x1 y1)). Qed.
Lemma lem1324928 (x1 : hreal) (y1 : hreal) : (term32 x1 y1) = (term30 x1 y1).
Proof. exact (EQ_MP (@lem1324927 x1 y1) (@lem1324918 x1 y1)). Qed.
Lemma lem1324929 (x1 : hreal) (y1 : hreal) (x2 : hreal) (y2 : hreal) : (term34 x1 y1 x2) = (term35 x1 y1 x2 y2).
Proof. exact (MK_COMB (@lem1324928 x1 y1) (@lem1324900 x2 y2)). Qed.
Lemma lem1324930 (x2 : hreal) (y2 : hreal) (x1 : hreal) (y1 : hreal) : (term35 x1 y1 x2 y2) = (term36 x2 y2 x1 y1).
Proof. exact (eq_refl (term35 x1 y1 x2 y2)). Qed.
Lemma lem1324931 (x1 : hreal) (y1 : hreal) (x2 : hreal) : (term37 x1 y1 x2) = (term37 x1 y1 x2).
Proof. exact (eq_refl (term37 x1 y1 x2)). Qed.
Lemma lem1324932 (x2 : hreal) (y2 : hreal) (x1 : hreal) (y1 : hreal) : ((term34 x1 y1 x2) = (term35 x1 y1 x2 y2)) = ((term34 x1 y1 x2) = (term36 x2 y2 x1 y1)).
Proof. exact (MK_COMB (@lem1324931 x1 y1 x2) (@lem1324930 x2 y2 x1 y1)). Qed.
Lemma lem1324933 (x1 : hreal) (x2 : hreal) (y1 : hreal) : (term34 x1 y1 x2) = (term38 x1 x2 y1).
Proof. exact (eq_refl (term34 x1 y1 x2)). Qed.
Lemma lem1324934 : (@eq (hreal -> Prop)) = (@eq (hreal -> Prop)).
Proof. exact (eq_refl (@eq (hreal -> Prop))). Qed.
Lemma lem1324935 (x1 : hreal) (x2 : hreal) (y1 : hreal) : (term37 x1 y1 x2) = (term39 x1 x2 y1).
Proof. exact (MK_COMB (@lem1324934) (@lem1324933 x1 x2 y1)). Qed.
Lemma lem1324936 (x2 : hreal) (y2 : hreal) (x1 : hreal) (y1 : hreal) : (term36 x2 y2 x1 y1) = (term36 x2 y2 x1 y1).
Proof. exact (eq_refl (term36 x2 y2 x1 y1)). Qed.
Lemma lem1324937 (x2 : hreal) (y2 : hreal) (x1 : hreal) (y1 : hreal) : ((term34 x1 y1 x2) = (term36 x2 y2 x1 y1)) = ((term38 x1 x2 y1) = (term36 x2 y2 x1 y1)).
Proof. exact (MK_COMB (@lem1324935 x1 x2 y1) (@lem1324936 x2 y2 x1 y1)). Qed.
Lemma lem1324938 (x2 : hreal) (y2 : hreal) (x1 : hreal) (y1 : hreal) : ((term34 x1 y1 x2) = (term35 x1 y1 x2 y2)) = ((term38 x1 x2 y1) = (term36 x2 y2 x1 y1)).
Proof. exact (TRANS (@lem1324932 x2 y2 x1 y1) (@lem1324937 x2 y2 x1 y1)). Qed.
Lemma lem1324939 (x2 : hreal) (y2 : hreal) (x1 : hreal) (y1 : hreal) : (term38 x1 x2 y1) = (term36 x2 y2 x1 y1).
Proof. exact (EQ_MP (@lem1324938 x2 y2 x1 y1) (@lem1324929 x1 y1 x2 y2)). Qed.
Lemma lem1324940 (x1 : hreal) (y1 : hreal) (x2 : hreal) (y2 : hreal) : (term40 x1 x2 y1 y2) = (term41 x1 y1 x2 y2).
Proof. exact (MK_COMB (@lem1324939 x2 y2 x1 y1) (@lem1324905 x2 y2)). Qed.
Lemma lem1324941 (x2 : hreal) (y2 : hreal) (x1 : hreal) (y1 : hreal) : (term41 x1 y1 x2 y2) = (term10 x2 y2 x1 y1).
Proof. exact (eq_refl (term41 x1 y1 x2 y2)). Qed.
Lemma lem1324942 (x1 : hreal) (x2 : hreal) (y1 : hreal) (y2 : hreal) : (term42 x1 x2 y1 y2) = (term42 x1 x2 y1 y2).
Proof. exact (eq_refl (term42 x1 x2 y1 y2)). Qed.
Lemma lem1324943 (x2 : hreal) (y2 : hreal) (x1 : hreal) (y1 : hreal) : ((term40 x1 x2 y1 y2) = (term41 x1 y1 x2 y2)) = ((term40 x1 x2 y1 y2) = (term10 x2 y2 x1 y1)).
Proof. exact (MK_COMB (@lem1324942 x1 x2 y1 y2) (@lem1324941 x2 y2 x1 y1)). Qed.
Lemma lem1324944 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : (term40 x1 x2 y1 y2) = (term43 x1 y2 x2 y1).
Proof. exact (eq_refl (term40 x1 x2 y1 y2)). Qed.
Lemma lem1324945 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1324946 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : (term42 x1 x2 y1 y2) = (term44 x1 y2 x2 y1).
Proof. exact (MK_COMB (@lem1324945) (@lem1324944 x1 y2 x2 y1)). Qed.
Lemma lem1324947 (x2 : hreal) (y2 : hreal) (x1 : hreal) (y1 : hreal) : (term10 x2 y2 x1 y1) = (term10 x2 y2 x1 y1).
Proof. exact (eq_refl (term10 x2 y2 x1 y1)). Qed.
Lemma lem1324948 (x2 : hreal) (y2 : hreal) (x1 : hreal) (y1 : hreal) : ((term40 x1 x2 y1 y2) = (term10 x2 y2 x1 y1)) = ((term43 x1 y2 x2 y1) = (term10 x2 y2 x1 y1)).
Proof. exact (MK_COMB (@lem1324946 x1 y2 x2 y1) (@lem1324947 x2 y2 x1 y1)). Qed.
Lemma lem1324949 (x2 : hreal) (y2 : hreal) (x1 : hreal) (y1 : hreal) : ((term40 x1 x2 y1 y2) = (term41 x1 y1 x2 y2)) = ((term43 x1 y2 x2 y1) = (term10 x2 y2 x1 y1)).
Proof. exact (TRANS (@lem1324943 x2 y2 x1 y1) (@lem1324948 x2 y2 x1 y1)). Qed.
Lemma lem1324950 (x2 : hreal) (y2 : hreal) (x1 : hreal) (y1 : hreal) : (term43 x1 y2 x2 y1) = (term10 x2 y2 x1 y1).
Proof. exact (EQ_MP (@lem1324949 x2 y2 x1 y1) (@lem1324940 x1 y1 x2 y2)). Qed.
Lemma lem1324951 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : (term10 x2 y2 x1 y1) = (term43 x1 y2 x2 y1).
Proof. exact (SYM (@lem1324950 x2 y2 x1 y1)). Qed.
Lemma lem1324952 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : (term9 x1 y1 x2 y2) = (term43 x1 y2 x2 y1).
Proof. exact (TRANS (@lem1324873 x2 y2 x1 y1) (@lem1324951 x1 y2 x2 y1)). Qed.
Lemma lem1324953 (x1 : hreal) (y2 : hreal) (x2 : hreal) : term45 x1 y2 x2.
Proof. exact (fun y1 : hreal => @lem1324952 x1 y2 x2 y1). Qed.
Lemma lem1324954 (x1 : hreal) (y2 : hreal) : term46 x1 y2.
Proof. exact (fun x2 : hreal => @lem1324953 x1 y2 x2). Qed.
Lemma lem1324955 (x1 : hreal) : term47 x1.
Proof. exact (fun y2 : hreal => @lem1324954 x1 y2). Qed.
Lemma lem1324956 : term48.
Proof. exact (fun x1 : hreal => @lem1324955 x1). Qed.
