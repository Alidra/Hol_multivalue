Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import TREAL_OF_NUM_LE_term_abbrevs.
Require Import HREAL_ADD_RID_spec.
Require Import thm0_spec.
Require Import thm1318876_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import treal_le_spec.
Require Import treal_of_num_spec.
Lemma lem1326944 (n : hreal) : term0 n.
Proof. exact (@lem1321694 n). Qed.
Lemma lem1326945 (n : hreal) : (term0 n) = ((term1 n) = n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem1326947 (m : nat) : term2 m.
Proof. exact (@lem1318876 m). Qed.
Lemma lem1326948 (m : nat) : (term2 m) = (term3 m).
Proof. exact (eq_refl (term2 m)). Qed.
Lemma lem1326949 (m : nat) : term3 m.
Proof. exact (EQ_MP (@lem1326948 m) (@lem1326947 m)). Qed.
Lemma lem1326950 (m : nat) (n : nat) : term4 m n.
Proof. exact (@lem1326949 m n). Qed.
Lemma lem1326951 (m : nat) (n : nat) : (term4 m n) = ((term5 m n) = (Peano.le m n)).
Proof. exact (eq_refl (term4 m n)). Qed.
Lemma lem1326953 (x1 : hreal) : term6 x1.
Proof. exact (@lem1324956 x1). Qed.
Lemma lem1326954 (x1 : hreal) : (term6 x1) = (term7 x1).
Proof. exact (eq_refl (term6 x1)). Qed.
Lemma lem1326955 (x1 : hreal) : term7 x1.
Proof. exact (EQ_MP (@lem1326954 x1) (@lem1326953 x1)). Qed.
Lemma lem1326956 (x1 : hreal) (y2 : hreal) : term8 x1 y2.
Proof. exact (@lem1326955 x1 y2). Qed.
Lemma lem1326957 (x1 : hreal) (y2 : hreal) : (term8 x1 y2) = (term9 x1 y2).
Proof. exact (eq_refl (term8 x1 y2)). Qed.
Lemma lem1326958 (x1 : hreal) (y2 : hreal) : term9 x1 y2.
Proof. exact (EQ_MP (@lem1326957 x1 y2) (@lem1326956 x1 y2)). Qed.
Lemma lem1326959 (x1 : hreal) (y2 : hreal) (x2 : hreal) : term10 x1 y2 x2.
Proof. exact (@lem1326958 x1 y2 x2). Qed.
Lemma lem1326960 (x1 : hreal) (y2 : hreal) (x2 : hreal) : (term10 x1 y2 x2) = (term11 x1 y2 x2).
Proof. exact (eq_refl (term10 x1 y2 x2)). Qed.
Lemma lem1326961 (x1 : hreal) (y2 : hreal) (x2 : hreal) : term11 x1 y2 x2.
Proof. exact (EQ_MP (@lem1326960 x1 y2 x2) (@lem1326959 x1 y2 x2)). Qed.
Lemma lem1326962 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : term12 x1 y2 x2 y1.
Proof. exact (@lem1326961 x1 y2 x2 y1). Qed.
Lemma lem1326963 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : (term12 x1 y2 x2 y1) = ((term13 x1 y1 x2 y2) = (term14 x1 y2 x2 y1)).
Proof. exact (eq_refl (term12 x1 y2 x2 y1)). Qed.
Lemma lem1326965 (n : nat) : term15 n.
Proof. exact (@lem1322742 n). Qed.
Lemma lem1326966 (n : nat) : (term15 n) = ((treal_of_num n) = (term16 n)).
Proof. exact (eq_refl (term15 n)). Qed.
Lemma lem1326979 (n : nat) : (treal_of_num n) = (term16 n).
Proof. exact (EQ_MP (@lem1326966 n) (@lem1326965 n)). Qed.
Lemma lem1326980 (m : nat) : (treal_of_num m) = (term16 m).
Proof. exact (@lem1326979 m). Qed.
Lemma lem1326981 : treal_le = treal_le.
Proof. exact (eq_refl treal_le). Qed.
Lemma lem1326982 (m : nat) : (term17 m) = (term18 m).
Proof. exact (MK_COMB (@lem1326981) (@lem1326980 m)). Qed.
Lemma lem1326984 (n : nat) : (treal_of_num n) = (term16 n).
Proof. exact (EQ_MP (@lem1326966 n) (@lem1326965 n)). Qed.
Lemma lem1326985 (m : nat) (n : nat) : (term19 m n) = (term20 m n).
Proof. exact (MK_COMB (@lem1326982 m) (@lem1326984 n)). Qed.
Lemma lem1326987 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : (term13 x1 y1 x2 y2) = (term14 x1 y2 x2 y1).
Proof. exact (EQ_MP (@lem1326963 x1 y2 x2 y1) (@lem1326962 x1 y2 x2 y1)). Qed.
Lemma lem1326988 (m : nat) (n : nat) : (term20 m n) = (term21 m n).
Proof. exact (@lem1326987 (hreal_of_num m) term22 (hreal_of_num n) term22). Qed.
Lemma lem1326990 (n : hreal) : (term1 n) = n.
Proof. exact (EQ_MP (@lem1326945 n) (@lem1326944 n)). Qed.
Lemma lem1326991 (m : nat) : (term23 m) = (hreal_of_num m).
Proof. exact (@lem1326990 (hreal_of_num m)). Qed.
Lemma lem1326992 : hreal_le = hreal_le.
Proof. exact (eq_refl hreal_le). Qed.
Lemma lem1326993 (m : nat) : (term24 m) = (term25 m).
Proof. exact (MK_COMB (@lem1326992) (@lem1326991 m)). Qed.
Lemma lem1326995 (n : hreal) : (term1 n) = n.
Proof. exact (EQ_MP (@lem1326945 n) (@lem1326944 n)). Qed.
Lemma lem1326996 (n : nat) : (term23 n) = (hreal_of_num n).
Proof. exact (@lem1326995 (hreal_of_num n)). Qed.
Lemma lem1326997 (m : nat) (n : nat) : (term21 m n) = (term5 m n).
Proof. exact (MK_COMB (@lem1326993 m) (@lem1326996 n)). Qed.
Lemma lem1326999 (m : nat) (n : nat) : (term5 m n) = (Peano.le m n).
Proof. exact (EQ_MP (@lem1326951 m n) (@lem1326950 m n)). Qed.
Lemma lem1327000 (m : nat) (n : nat) : (term21 m n) = (Peano.le m n).
Proof. exact (TRANS (@lem1326997 m n) (@lem1326999 m n)). Qed.
Lemma lem1327001 (m : nat) (n : nat) : (term20 m n) = (Peano.le m n).
Proof. exact (TRANS (@lem1326988 m n) (@lem1327000 m n)). Qed.
Lemma lem1327002 (m : nat) (n : nat) : (term19 m n) = (Peano.le m n).
Proof. exact (TRANS (@lem1326985 m n) (@lem1327001 m n)). Qed.
Lemma lem1327003 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1327004 (m : nat) (n : nat) : (term26 m n) = (term27 m n).
Proof. exact (MK_COMB (@lem1327003) (@lem1327002 m n)). Qed.
Lemma lem1327005 (m : nat) (n : nat) : (Peano.le m n) = (Peano.le m n).
Proof. exact (eq_refl (Peano.le m n)). Qed.
Lemma lem1327006 (m : nat) (n : nat) : ((term19 m n) = (Peano.le m n)) = ((Peano.le m n) = (Peano.le m n)).
Proof. exact (MK_COMB (@lem1327004 m n) (@lem1327005 m n)). Qed.
Lemma lem1327008 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1327009 (x : Prop) : (x = x) = True.
Proof. exact (@lem1327008 Prop x). Qed.
Lemma lem1327010 (m : nat) (n : nat) : ((Peano.le m n) = (Peano.le m n)) = True.
Proof. exact (@lem1327009 (Peano.le m n)). Qed.
Lemma lem1327011 (m : nat) (n : nat) : ((term19 m n) = (Peano.le m n)) = True.
Proof. exact (TRANS (@lem1327006 m n) (@lem1327010 m n)). Qed.
Lemma lem1327012 (m : nat) : (term28 m) = term29.
Proof. exact (fun_ext (fun n : nat => @lem1327011 m n)). Qed.
Lemma lem1327013 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1327014 (m : nat) : (term30 m) = term31.
Proof. exact (MK_COMB (@lem1327013) (@lem1327012 m)). Qed.
Lemma lem1327016 {A : Type'} (t : Prop) : (term32 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1327017 (t : Prop) : (term33 t) = t.
Proof. exact (@lem1327016 nat t). Qed.
Lemma lem1327018 : term31 = True.
Proof. exact (@lem1327017 True). Qed.
Lemma lem1327019 (m : nat) : (term30 m) = True.
Proof. exact (TRANS (@lem1327014 m) (@lem1327018)). Qed.
Lemma lem1327020 : term34 = term29.
Proof. exact (fun_ext (fun m : nat => @lem1327019 m)). Qed.
Lemma lem1327021 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1327022 : term35 = term31.
Proof. exact (MK_COMB (@lem1327021) (@lem1327020)). Qed.
Lemma lem1327024 {A : Type'} (t : Prop) : (term32 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1327025 (t : Prop) : (term33 t) = t.
Proof. exact (@lem1327024 nat t). Qed.
Lemma lem1327026 : term31 = True.
Proof. exact (@lem1327025 True). Qed.
Lemma lem1327027 : term35 = True.
Proof. exact (TRANS (@lem1327022) (@lem1327026)). Qed.
Lemma lem1327028 : True = term35.
Proof. exact (SYM (@lem1327027)). Qed.
Lemma lem1327029 : term35.
Proof. exact (EQ_MP (@lem1327028) (@lem0)). Qed.
