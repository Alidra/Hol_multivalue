Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1340049_term_abbrevs.
Require Import TREAL_LE_MUL_spec.
Require Import thm1337531_spec.
Require Import thm1337536_spec.
Require Import thm1337872_spec.
Require Import thm1337877_spec.
Require Import thm1337985_spec.
Require Import thm1337990_spec.
Require Import thm1338105_spec.
Require Import thm1338106_spec.
Lemma lem1339933 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : (treal_le x1 y1) = (term0 x1 y1).
Proof. exact (EQ_MP (@lem1337990 x1 y1) (@lem1337985 x1 y1)). Qed.
Lemma lem1339934 (x : prod hreal hreal) : (term1 x) = (term2 x).
Proof. exact (@lem1339933 term3 x). Qed.
Lemma lem1339936 (m : nat) : (term4 m) = (real_of_num m).
Proof. exact (EQ_MP (@lem1337536 m) (@lem1337531 m)). Qed.
Lemma lem1339937 : term5 = term6.
Proof. exact (@lem1339936 (NUMERAL 0)). Qed.
Lemma lem1339938 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem1339939 : term7 = term8.
Proof. exact (MK_COMB (@lem1339938) (@lem1339937)). Qed.
Lemma lem1339940 (x : prod hreal hreal) : (term9 x) = (term9 x).
Proof. exact (eq_refl (term9 x)). Qed.
Lemma lem1339941 (x : prod hreal hreal) : (term2 x) = (term10 x).
Proof. exact (MK_COMB (@lem1339939) (@lem1339940 x)). Qed.
Lemma lem1339942 (x : prod hreal hreal) : (term1 x) = (term10 x).
Proof. exact (TRANS (@lem1339934 x) (@lem1339941 x)). Qed.
Lemma lem1339943 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1339944 (x : prod hreal hreal) : (term11 x) = (term12 x).
Proof. exact (MK_COMB (@lem1339943) (@lem1339942 x)). Qed.
Lemma lem1339946 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : (treal_le x1 y1) = (term0 x1 y1).
Proof. exact (EQ_MP (@lem1337990 x1 y1) (@lem1337985 x1 y1)). Qed.
Lemma lem1339947 (y : prod hreal hreal) : (term1 y) = (term2 y).
Proof. exact (@lem1339946 term3 y). Qed.
Lemma lem1339949 (m : nat) : (term4 m) = (real_of_num m).
Proof. exact (EQ_MP (@lem1337536 m) (@lem1337531 m)). Qed.
Lemma lem1339950 : term5 = term6.
Proof. exact (@lem1339949 (NUMERAL 0)). Qed.
Lemma lem1339951 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem1339952 : term7 = term8.
Proof. exact (MK_COMB (@lem1339951) (@lem1339950)). Qed.
Lemma lem1339953 (y : prod hreal hreal) : (term9 y) = (term9 y).
Proof. exact (eq_refl (term9 y)). Qed.
Lemma lem1339954 (y : prod hreal hreal) : (term2 y) = (term10 y).
Proof. exact (MK_COMB (@lem1339952) (@lem1339953 y)). Qed.
Lemma lem1339955 (y : prod hreal hreal) : (term1 y) = (term10 y).
Proof. exact (TRANS (@lem1339947 y) (@lem1339954 y)). Qed.
Lemma lem1339956 (x : prod hreal hreal) (y : prod hreal hreal) : (term13 x y) = (term14 x y).
Proof. exact (MK_COMB (@lem1339944 x) (@lem1339955 y)). Qed.
Lemma lem1339959 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1339960 (x : prod hreal hreal) (y : prod hreal hreal) : (term15 x y) = (term16 x y).
Proof. exact (MK_COMB (@lem1339959) (@lem1339956 x y)). Qed.
Lemma lem1339962 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : (treal_le x1 y1) = (term0 x1 y1).
Proof. exact (EQ_MP (@lem1337990 x1 y1) (@lem1337985 x1 y1)). Qed.
Lemma lem1339963 (x : prod hreal hreal) (y : prod hreal hreal) : (term17 x y) = (term18 x y).
Proof. exact (@lem1339962 term3 (treal_mul x y)). Qed.
Lemma lem1339965 (m : nat) : (term4 m) = (real_of_num m).
Proof. exact (EQ_MP (@lem1337536 m) (@lem1337531 m)). Qed.
Lemma lem1339966 : term5 = term6.
Proof. exact (@lem1339965 (NUMERAL 0)). Qed.
Lemma lem1339967 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem1339968 : term7 = term8.
Proof. exact (MK_COMB (@lem1339967) (@lem1339966)). Qed.
Lemma lem1339970 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : (term19 x1 y1) = (term20 x1 y1).
Proof. exact (EQ_MP (@lem1337877 x1 y1) (@lem1337872 x1 y1)). Qed.
Lemma lem1339971 (x : prod hreal hreal) (y : prod hreal hreal) : (term19 x y) = (term20 x y).
Proof. exact (@lem1339970 x y). Qed.
Lemma lem1339972 (x : prod hreal hreal) (y : prod hreal hreal) : (term18 x y) = (term21 x y).
Proof. exact (MK_COMB (@lem1339968) (@lem1339971 x y)). Qed.
Lemma lem1339973 (x : prod hreal hreal) (y : prod hreal hreal) : (term17 x y) = (term21 x y).
Proof. exact (TRANS (@lem1339963 x y) (@lem1339972 x y)). Qed.
Lemma lem1339974 (x : prod hreal hreal) (y : prod hreal hreal) : (term22 x y) = (term23 x y).
Proof. exact (MK_COMB (@lem1339960 x y) (@lem1339973 x y)). Qed.
Lemma lem1339977 (x : prod hreal hreal) : (term24 x) = (term25 x).
Proof. exact (fun_ext (fun y : prod hreal hreal => @lem1339974 x y)). Qed.
Lemma lem1339978 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1339979 (x : prod hreal hreal) : (term26 x) = (term27 x).
Proof. exact (MK_COMB (@lem1339978) (@lem1339977 x)). Qed.
Lemma lem1339985 (P : real -> Prop) : (term28 P) = (term29 P).
Proof. exact (EQ_MP (@lem1338106 P) (@lem1338105 P)). Qed.
Lemma lem1339986 (x : prod hreal hreal) : (term30 x) = (term31 x).
Proof. exact (@lem1339985 (term32 x)). Qed.
Lemma lem1339987 (x : prod hreal hreal) (y : prod hreal hreal) : (term33 x y) = (term23 x y).
Proof. exact (eq_refl (term33 x y)). Qed.
Lemma lem1339988 (x : prod hreal hreal) : (term34 x) = (term25 x).
Proof. exact (fun_ext (fun y : prod hreal hreal => @lem1339987 x y)). Qed.
Lemma lem1339989 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1339990 (x : prod hreal hreal) : (term30 x) = (term27 x).
Proof. exact (MK_COMB (@lem1339989) (@lem1339988 x)). Qed.
Lemma lem1339991 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1339992 (x : prod hreal hreal) : (term35 x) = (term36 x).
Proof. exact (MK_COMB (@lem1339991) (@lem1339990 x)). Qed.
Lemma lem1339993 (x : prod hreal hreal) (y : real) : (term37 x y) = (term38 x y).
Proof. exact (eq_refl (term37 x y)). Qed.
Lemma lem1339994 (x : prod hreal hreal) : (term39 x) = (term32 x).
Proof. exact (fun_ext (fun y : real => @lem1339993 x y)). Qed.
Lemma lem1339995 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1339996 (x : prod hreal hreal) : (term31 x) = (term40 x).
Proof. exact (MK_COMB (@lem1339995) (@lem1339994 x)). Qed.
Lemma lem1339997 (x : prod hreal hreal) : ((term30 x) = (term31 x)) = ((term27 x) = (term40 x)).
Proof. exact (MK_COMB (@lem1339992 x) (@lem1339996 x)). Qed.
Lemma lem1339998 (x : prod hreal hreal) : (term27 x) = (term40 x).
Proof. exact (EQ_MP (@lem1339997 x) (@lem1339986 x)). Qed.
Lemma lem1340009 (x : prod hreal hreal) : (term26 x) = (term40 x).
Proof. exact (TRANS (@lem1339979 x) (@lem1339998 x)). Qed.
Lemma lem1340010 : term41 = term42.
Proof. exact (fun_ext (fun x : prod hreal hreal => @lem1340009 x)). Qed.
Lemma lem1340011 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1340012 : term43 = term44.
Proof. exact (MK_COMB (@lem1340011) (@lem1340010)). Qed.
Lemma lem1340018 (P : real -> Prop) : (term28 P) = (term29 P).
Proof. exact (EQ_MP (@lem1338106 P) (@lem1338105 P)). Qed.
Lemma lem1340019 : term45 = term46.
Proof. exact (@lem1340018 term47). Qed.
Lemma lem1340020 (x : prod hreal hreal) : (term48 x) = (term40 x).
Proof. exact (eq_refl (term48 x)). Qed.
Lemma lem1340021 : term49 = term42.
Proof. exact (fun_ext (fun x : prod hreal hreal => @lem1340020 x)). Qed.
Lemma lem1340022 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1340023 : term45 = term44.
Proof. exact (MK_COMB (@lem1340022) (@lem1340021)). Qed.
Lemma lem1340024 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1340025 : term50 = term51.
Proof. exact (MK_COMB (@lem1340024) (@lem1340023)). Qed.
Lemma lem1340026 (x : real) : (term52 x) = (term53 x).
Proof. exact (eq_refl (term52 x)). Qed.
Lemma lem1340027 : term54 = term47.
Proof. exact (fun_ext (fun x : real => @lem1340026 x)). Qed.
Lemma lem1340028 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1340029 : term46 = term55.
Proof. exact (MK_COMB (@lem1340028) (@lem1340027)). Qed.
Lemma lem1340030 : (term45 = term46) = (term44 = term55).
Proof. exact (MK_COMB (@lem1340025) (@lem1340029)). Qed.
Lemma lem1340031 : term44 = term55.
Proof. exact (EQ_MP (@lem1340030) (@lem1340019)). Qed.
Lemma lem1340048 : term43 = term55.
Proof. exact (TRANS (@lem1340012) (@lem1340031)). Qed.
Lemma lem1340049 : term55.
Proof. exact (EQ_MP (@lem1340048) (@lem1331691)). Qed.
