Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1338986_term_abbrevs.
Require Import TREAL_MUL_LID_spec.
Require Import thm1337531_spec.
Require Import thm1337536_spec.
Require Import thm1337872_spec.
Require Import thm1337877_spec.
Require Import thm1338105_spec.
Require Import thm1338106_spec.
Require Import thm1338112_spec.
Require Import thm1338113_spec.
Lemma lem1338933 (x : prod hreal hreal) (y : prod hreal hreal) : (treal_eq x y) = ((term0 x) = (term0 y)).
Proof. exact (EQ_MP (@lem1338113 x y) (@lem1338112 x y)). Qed.
Lemma lem1338934 (x : prod hreal hreal) : (term1 x) = ((term2 x) = (term0 x)).
Proof. exact (@lem1338933 (term3 x) x). Qed.
Lemma lem1338938 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : (term4 x1 y1) = (term5 x1 y1).
Proof. exact (EQ_MP (@lem1337877 x1 y1) (@lem1337872 x1 y1)). Qed.
Lemma lem1338939 (x : prod hreal hreal) : (term2 x) = (term6 x).
Proof. exact (@lem1338938 term7 x). Qed.
Lemma lem1338941 (m : nat) : (term8 m) = (real_of_num m).
Proof. exact (EQ_MP (@lem1337536 m) (@lem1337531 m)). Qed.
Lemma lem1338942 : term9 = term10.
Proof. exact (@lem1338941 term11). Qed.
Lemma lem1338943 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1338944 : term12 = term13.
Proof. exact (MK_COMB (@lem1338943) (@lem1338942)). Qed.
Lemma lem1338945 (x : prod hreal hreal) : (term0 x) = (term0 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1338946 (x : prod hreal hreal) : (term6 x) = (term14 x).
Proof. exact (MK_COMB (@lem1338944) (@lem1338945 x)). Qed.
Lemma lem1338947 (x : prod hreal hreal) : (term2 x) = (term14 x).
Proof. exact (TRANS (@lem1338939 x) (@lem1338946 x)). Qed.
Lemma lem1338948 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1338949 (x : prod hreal hreal) : (term15 x) = (term16 x).
Proof. exact (MK_COMB (@lem1338948) (@lem1338947 x)). Qed.
Lemma lem1338950 (x : prod hreal hreal) : (term0 x) = (term0 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1338951 (x : prod hreal hreal) : ((term2 x) = (term0 x)) = ((term14 x) = (term0 x)).
Proof. exact (MK_COMB (@lem1338949 x) (@lem1338950 x)). Qed.
Lemma lem1338954 (x : prod hreal hreal) : (term1 x) = ((term14 x) = (term0 x)).
Proof. exact (TRANS (@lem1338934 x) (@lem1338951 x)). Qed.
Lemma lem1338955 : term17 = term18.
Proof. exact (fun_ext (fun x : prod hreal hreal => @lem1338954 x)). Qed.
Lemma lem1338956 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1338957 : term19 = term20.
Proof. exact (MK_COMB (@lem1338956) (@lem1338955)). Qed.
Lemma lem1338963 (P : real -> Prop) : (term21 P) = (term22 P).
Proof. exact (EQ_MP (@lem1338106 P) (@lem1338105 P)). Qed.
Lemma lem1338964 : term23 = term24.
Proof. exact (@lem1338963 term25). Qed.
Lemma lem1338965 (x : prod hreal hreal) : (term26 x) = ((term14 x) = (term0 x)).
Proof. exact (eq_refl (term26 x)). Qed.
Lemma lem1338966 : term27 = term18.
Proof. exact (fun_ext (fun x : prod hreal hreal => @lem1338965 x)). Qed.
Lemma lem1338967 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1338968 : term23 = term20.
Proof. exact (MK_COMB (@lem1338967) (@lem1338966)). Qed.
Lemma lem1338969 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1338970 : term28 = term29.
Proof. exact (MK_COMB (@lem1338969) (@lem1338968)). Qed.
Lemma lem1338971 (x : real) : (term30 x) = ((term31 x) = x).
Proof. exact (eq_refl (term30 x)). Qed.
Lemma lem1338972 : term32 = term25.
Proof. exact (fun_ext (fun x : real => @lem1338971 x)). Qed.
Lemma lem1338973 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1338974 : term24 = term33.
Proof. exact (MK_COMB (@lem1338973) (@lem1338972)). Qed.
Lemma lem1338975 : (term23 = term24) = (term20 = term33).
Proof. exact (MK_COMB (@lem1338970) (@lem1338974)). Qed.
Lemma lem1338976 : term20 = term33.
Proof. exact (EQ_MP (@lem1338975) (@lem1338964)). Qed.
Lemma lem1338985 : term19 = term33.
Proof. exact (TRANS (@lem1338957) (@lem1338976)). Qed.
Lemma lem1338986 : term33.
Proof. exact (EQ_MP (@lem1338985) (@lem1329299)). Qed.
