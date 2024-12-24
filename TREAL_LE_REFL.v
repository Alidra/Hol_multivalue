Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import TREAL_LE_REFL_term_abbrevs.
Require Import FORALL_PAIR_THM_spec.
Require Import thm0_spec.
Require Import thm1319042_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm7_spec.
Require Import treal_le_spec.
Lemma lem1329891 (x : hreal) : term0 x.
Proof. exact (@lem1319042 x). Qed.
Lemma lem1329892 (x : hreal) : (term0 x) = (hreal_le x x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1329893 (x : hreal) : hreal_le x x.
Proof. exact (EQ_MP (@lem1329892 x) (@lem1329891 x)). Qed.
Lemma lem1329894 (x : hreal) : (hreal_le x x) = ((hreal_le x x) = True).
Proof. exact (@lem7 (hreal_le x x)). Qed.
Lemma lem1329896 (x1 : hreal) : term1 x1.
Proof. exact (@lem1324956 x1). Qed.
Lemma lem1329897 (x1 : hreal) : (term1 x1) = (term2 x1).
Proof. exact (eq_refl (term1 x1)). Qed.
Lemma lem1329898 (x1 : hreal) : term2 x1.
Proof. exact (EQ_MP (@lem1329897 x1) (@lem1329896 x1)). Qed.
Lemma lem1329899 (x1 : hreal) (y2 : hreal) : term3 x1 y2.
Proof. exact (@lem1329898 x1 y2). Qed.
Lemma lem1329900 (x1 : hreal) (y2 : hreal) : (term3 x1 y2) = (term4 x1 y2).
Proof. exact (eq_refl (term3 x1 y2)). Qed.
Lemma lem1329901 (x1 : hreal) (y2 : hreal) : term4 x1 y2.
Proof. exact (EQ_MP (@lem1329900 x1 y2) (@lem1329899 x1 y2)). Qed.
Lemma lem1329902 (x1 : hreal) (y2 : hreal) (x2 : hreal) : term5 x1 y2 x2.
Proof. exact (@lem1329901 x1 y2 x2). Qed.
Lemma lem1329903 (x1 : hreal) (y2 : hreal) (x2 : hreal) : (term5 x1 y2 x2) = (term6 x1 y2 x2).
Proof. exact (eq_refl (term5 x1 y2 x2)). Qed.
Lemma lem1329904 (x1 : hreal) (y2 : hreal) (x2 : hreal) : term6 x1 y2 x2.
Proof. exact (EQ_MP (@lem1329903 x1 y2 x2) (@lem1329902 x1 y2 x2)). Qed.
Lemma lem1329905 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : term7 x1 y2 x2 y1.
Proof. exact (@lem1329904 x1 y2 x2 y1). Qed.
Lemma lem1329906 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : (term7 x1 y2 x2 y1) = ((term8 x1 y1 x2 y2) = (term9 x1 y2 x2 y1)).
Proof. exact (eq_refl (term7 x1 y2 x2 y1)). Qed.
Lemma lem1329908 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : term10 _5106 _5107 P.
Proof. exact (@lem49909 _5106 _5107 P). Qed.
Lemma lem1329909 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term10 _5106 _5107 P) = ((term11 _5106 _5107 P) = (term12 _5106 _5107 P)).
Proof. exact (eq_refl (term10 _5106 _5107 P)). Qed.
Lemma lem1329916 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term11 _5106 _5107 P) = (term12 _5106 _5107 P).
Proof. exact (EQ_MP (@lem1329909 _5106 _5107 P) (@lem1329908 _5106 _5107 P)). Qed.
Lemma lem1329917 (P : type1233) : (term13 P) = (term14 P).
Proof. exact (@lem1329916 hreal hreal P). Qed.
Lemma lem1329918 : term15 = term16.
Proof. exact (@lem1329917 term17). Qed.
Lemma lem1329919 (x : prod hreal hreal) : (term18 x) = (treal_le x x).
Proof. exact (eq_refl (term18 x)). Qed.
Lemma lem1329920 : term19 = term17.
Proof. exact (fun_ext (fun x : prod hreal hreal => @lem1329919 x)). Qed.
Lemma lem1329921 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1329922 : term15 = term20.
Proof. exact (MK_COMB (@lem1329921) (@lem1329920)). Qed.
Lemma lem1329923 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1329924 : term21 = term22.
Proof. exact (MK_COMB (@lem1329923) (@lem1329922)). Qed.
Lemma lem1329925 (p1 : hreal) (p2 : hreal) : (term23 p1 p2) = (term24 p1 p2).
Proof. exact (eq_refl (term23 p1 p2)). Qed.
Lemma lem1329926 (p1 : hreal) : (term25 p1) = (term26 p1).
Proof. exact (fun_ext (fun p2 : hreal => @lem1329925 p1 p2)). Qed.
Lemma lem1329927 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1329928 (p1 : hreal) : (term27 p1) = (term28 p1).
Proof. exact (MK_COMB (@lem1329927) (@lem1329926 p1)). Qed.
Lemma lem1329929 : term29 = term30.
Proof. exact (fun_ext (fun p1 : hreal => @lem1329928 p1)). Qed.
Lemma lem1329930 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1329931 : term16 = term31.
Proof. exact (MK_COMB (@lem1329930) (@lem1329929)). Qed.
Lemma lem1329932 : (term15 = term16) = (term20 = term31).
Proof. exact (MK_COMB (@lem1329924) (@lem1329931)). Qed.
Lemma lem1329933 : term20 = term31.
Proof. exact (EQ_MP (@lem1329932) (@lem1329918)). Qed.
Lemma lem1329947 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : (term8 x1 y1 x2 y2) = (term9 x1 y2 x2 y1).
Proof. exact (EQ_MP (@lem1329906 x1 y2 x2 y1) (@lem1329905 x1 y2 x2 y1)). Qed.
Lemma lem1329948 (p1 : hreal) (p2 : hreal) : (term24 p1 p2) = (term32 p1 p2).
Proof. exact (@lem1329947 p1 p2 p1 p2). Qed.
Lemma lem1329950 (x : hreal) : (hreal_le x x) = True.
Proof. exact (EQ_MP (@lem1329894 x) (@lem1329893 x)). Qed.
Lemma lem1329951 (p1 : hreal) (p2 : hreal) : (term32 p1 p2) = True.
Proof. exact (@lem1329950 (hreal_add p1 p2)). Qed.
Lemma lem1329952 (p1 : hreal) (p2 : hreal) : (term24 p1 p2) = True.
Proof. exact (TRANS (@lem1329948 p1 p2) (@lem1329951 p1 p2)). Qed.
Lemma lem1329953 (p1 : hreal) : (term26 p1) = term33.
Proof. exact (fun_ext (fun p2 : hreal => @lem1329952 p1 p2)). Qed.
Lemma lem1329954 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1329955 (p1 : hreal) : (term28 p1) = term34.
Proof. exact (MK_COMB (@lem1329954) (@lem1329953 p1)). Qed.
Lemma lem1329957 {A : Type'} (t : Prop) : (term35 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1329958 (t : Prop) : (term36 t) = t.
Proof. exact (@lem1329957 hreal t). Qed.
Lemma lem1329959 : term34 = True.
Proof. exact (@lem1329958 True). Qed.
Lemma lem1329960 (p1 : hreal) : (term28 p1) = True.
Proof. exact (TRANS (@lem1329955 p1) (@lem1329959)). Qed.
Lemma lem1329961 : term30 = term33.
Proof. exact (fun_ext (fun p1 : hreal => @lem1329960 p1)). Qed.
Lemma lem1329962 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1329963 : term31 = term34.
Proof. exact (MK_COMB (@lem1329962) (@lem1329961)). Qed.
Lemma lem1329965 {A : Type'} (t : Prop) : (term35 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1329966 (t : Prop) : (term36 t) = t.
Proof. exact (@lem1329965 hreal t). Qed.
Lemma lem1329967 : term34 = True.
Proof. exact (@lem1329966 True). Qed.
Lemma lem1329968 : term31 = True.
Proof. exact (TRANS (@lem1329963) (@lem1329967)). Qed.
Lemma lem1329969 : term20 = True.
Proof. exact (TRANS (@lem1329933) (@lem1329968)). Qed.
Lemma lem1329970 : True = term20.
Proof. exact (SYM (@lem1329969)). Qed.
Lemma lem1329971 : term20.
Proof. exact (EQ_MP (@lem1329970) (@lem0)). Qed.
