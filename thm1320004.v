Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1320004_term_abbrevs.
Require Import NADD_ADD_SYM_spec.
Require Import thm1317906_spec.
Require Import thm1317911_spec.
Require Import thm1318759_spec.
Require Import thm1318760_spec.
Require Import thm1318766_spec.
Require Import thm1318767_spec.
Lemma lem1319921 (x : nadd) (y : nadd) : (nadd_eq x y) = ((term0 x) = (term0 y)).
Proof. exact (EQ_MP (@lem1318767 x y) (@lem1318766 x y)). Qed.
Lemma lem1319922 (y : nadd) (x : nadd) : (term1 y x) = ((term2 x y) = (term2 y x)).
Proof. exact (@lem1319921 (nadd_add x y) (nadd_add y x)). Qed.
Lemma lem1319926 (x : nadd) (y : nadd) : (term2 x y) = (term3 x y).
Proof. exact (EQ_MP (@lem1317911 x y) (@lem1317906 x y)). Qed.
Lemma lem1319927 : (@eq hreal) = (@eq hreal).
Proof. exact (eq_refl (@eq hreal)). Qed.
Lemma lem1319928 (x : nadd) (y : nadd) : (term4 x y) = (term5 x y).
Proof. exact (MK_COMB (@lem1319927) (@lem1319926 x y)). Qed.
Lemma lem1319930 (x : nadd) (y : nadd) : (term2 x y) = (term3 x y).
Proof. exact (EQ_MP (@lem1317911 x y) (@lem1317906 x y)). Qed.
Lemma lem1319931 (y : nadd) (x : nadd) : (term2 y x) = (term3 y x).
Proof. exact (@lem1319930 y x). Qed.
Lemma lem1319932 (y : nadd) (x : nadd) : ((term2 x y) = (term2 y x)) = ((term3 x y) = (term3 y x)).
Proof. exact (MK_COMB (@lem1319928 x y) (@lem1319931 y x)). Qed.
Lemma lem1319935 (y : nadd) (x : nadd) : (term1 y x) = ((term3 x y) = (term3 y x)).
Proof. exact (TRANS (@lem1319922 y x) (@lem1319932 y x)). Qed.
Lemma lem1319936 (x : nadd) : (term6 x) = (term7 x).
Proof. exact (fun_ext (fun y : nadd => @lem1319935 y x)). Qed.
Lemma lem1319937 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1319938 (x : nadd) : (term8 x) = (term9 x).
Proof. exact (MK_COMB (@lem1319937) (@lem1319936 x)). Qed.
Lemma lem1319944 (P : hreal -> Prop) : (term10 P) = (term11 P).
Proof. exact (EQ_MP (@lem1318760 P) (@lem1318759 P)). Qed.
Lemma lem1319945 (x : nadd) : (term12 x) = (term13 x).
Proof. exact (@lem1319944 (term14 x)). Qed.
Lemma lem1319946 (y : nadd) (x : nadd) : (term15 x y) = ((term3 x y) = (term3 y x)).
Proof. exact (eq_refl (term15 x y)). Qed.
Lemma lem1319947 (x : nadd) : (term16 x) = (term7 x).
Proof. exact (fun_ext (fun y : nadd => @lem1319946 y x)). Qed.
Lemma lem1319948 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1319949 (x : nadd) : (term12 x) = (term9 x).
Proof. exact (MK_COMB (@lem1319948) (@lem1319947 x)). Qed.
Lemma lem1319950 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1319951 (x : nadd) : (term17 x) = (term18 x).
Proof. exact (MK_COMB (@lem1319950) (@lem1319949 x)). Qed.
Lemma lem1319952 (y : hreal) (x : nadd) : (term19 x y) = ((term20 x y) = (term21 y x)).
Proof. exact (eq_refl (term19 x y)). Qed.
Lemma lem1319953 (x : nadd) : (term22 x) = (term14 x).
Proof. exact (fun_ext (fun y : hreal => @lem1319952 y x)). Qed.
Lemma lem1319954 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1319955 (x : nadd) : (term13 x) = (term23 x).
Proof. exact (MK_COMB (@lem1319954) (@lem1319953 x)). Qed.
Lemma lem1319956 (x : nadd) : ((term12 x) = (term13 x)) = ((term9 x) = (term23 x)).
Proof. exact (MK_COMB (@lem1319951 x) (@lem1319955 x)). Qed.
Lemma lem1319957 (x : nadd) : (term9 x) = (term23 x).
Proof. exact (EQ_MP (@lem1319956 x) (@lem1319945 x)). Qed.
Lemma lem1319966 (x : nadd) : (term8 x) = (term23 x).
Proof. exact (TRANS (@lem1319938 x) (@lem1319957 x)). Qed.
Lemma lem1319967 : term24 = term25.
Proof. exact (fun_ext (fun x : nadd => @lem1319966 x)). Qed.
Lemma lem1319968 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1319969 : term26 = term27.
Proof. exact (MK_COMB (@lem1319968) (@lem1319967)). Qed.
Lemma lem1319975 (P : hreal -> Prop) : (term10 P) = (term11 P).
Proof. exact (EQ_MP (@lem1318760 P) (@lem1318759 P)). Qed.
Lemma lem1319976 : term28 = term29.
Proof. exact (@lem1319975 term30). Qed.
Lemma lem1319977 (x : nadd) : (term31 x) = (term23 x).
Proof. exact (eq_refl (term31 x)). Qed.
Lemma lem1319978 : term32 = term25.
Proof. exact (fun_ext (fun x : nadd => @lem1319977 x)). Qed.
Lemma lem1319979 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1319980 : term28 = term27.
Proof. exact (MK_COMB (@lem1319979) (@lem1319978)). Qed.
Lemma lem1319981 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1319982 : term33 = term34.
Proof. exact (MK_COMB (@lem1319981) (@lem1319980)). Qed.
Lemma lem1319983 (x : hreal) : (term35 x) = (term36 x).
Proof. exact (eq_refl (term35 x)). Qed.
Lemma lem1319984 : term37 = term30.
Proof. exact (fun_ext (fun x : hreal => @lem1319983 x)). Qed.
Lemma lem1319985 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1319986 : term29 = term38.
Proof. exact (MK_COMB (@lem1319985) (@lem1319984)). Qed.
Lemma lem1319987 : (term28 = term29) = (term27 = term38).
Proof. exact (MK_COMB (@lem1319982) (@lem1319986)). Qed.
Lemma lem1319988 : term27 = term38.
Proof. exact (EQ_MP (@lem1319987) (@lem1319976)). Qed.
Lemma lem1320003 : term26 = term38.
Proof. exact (TRANS (@lem1319969) (@lem1319988)). Qed.
Lemma lem1320004 : term38.
Proof. exact (EQ_MP (@lem1320003) (@lem1274476)). Qed.
