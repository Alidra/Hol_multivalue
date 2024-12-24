Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_POW_ONE_term_abbrevs.
Require Import thm0_spec.
Require Import thm1338986_spec.
Require Import thm1344310_spec.
Require Import thm1344311_spec.
Require Import thm1344313_spec.
Require Import thm1344314_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Lemma lem1631007 (P : nat -> Prop) : term0 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem1631008 : term1.
Proof. exact (@lem1631007 term2). Qed.
Lemma lem1631009 : term3 = (term4 = term5).
Proof. exact (eq_refl term3). Qed.
Lemma lem1631010 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1631011 : term6 = term7.
Proof. exact (MK_COMB (@lem1631010) (@lem1631009)). Qed.
Lemma lem1631012 (n : nat) : (term8 n) = ((term9 n) = term5).
Proof. exact (eq_refl (term8 n)). Qed.
Lemma lem1631013 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1631014 (n : nat) : (term10 n) = (term11 n).
Proof. exact (MK_COMB (@lem1631013) (@lem1631012 n)). Qed.
Lemma lem1631015 (n : nat) : (term12 n) = ((term13 n) = term5).
Proof. exact (eq_refl (term12 n)). Qed.
Lemma lem1631016 (n : nat) : (term14 n) = (term15 n).
Proof. exact (MK_COMB (@lem1631014 n) (@lem1631015 n)). Qed.
Lemma lem1631017 : term16 = term17.
Proof. exact (fun_ext (fun n : nat => @lem1631016 n)). Qed.
Lemma lem1631018 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1631019 : term18 = term19.
Proof. exact (MK_COMB (@lem1631018) (@lem1631017)). Qed.
Lemma lem1631020 : term20 = term21.
Proof. exact (MK_COMB (@lem1631011) (@lem1631019)). Qed.
Lemma lem1631021 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1631022 : term22 = term23.
Proof. exact (MK_COMB (@lem1631021) (@lem1631020)). Qed.
Lemma lem1631023 (n : nat) : (term8 n) = ((term9 n) = term5).
Proof. exact (eq_refl (term8 n)). Qed.
Lemma lem1631024 : term24 = term2.
Proof. exact (fun_ext (fun n : nat => @lem1631023 n)). Qed.
Lemma lem1631025 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1631026 : term25 = term26.
Proof. exact (MK_COMB (@lem1631025) (@lem1631024)). Qed.
Lemma lem1631027 : term1 = term27.
Proof. exact (MK_COMB (@lem1631022) (@lem1631026)). Qed.
Lemma lem1631028 : term27.
Proof. exact (EQ_MP (@lem1631027) (@lem1631008)). Qed.
Lemma lem1631041 (x : real) : (term28 x) = term5.
Proof. exact (EQ_MP (@lem1344311 x) (@lem1344310 x)). Qed.
Lemma lem1631042 : term4 = term5.
Proof. exact (@lem1631041 term5). Qed.
Lemma lem1631043 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1631044 : term29 = term30.
Proof. exact (MK_COMB (@lem1631043) (@lem1631042)). Qed.
Lemma lem1631045 : term5 = term5.
Proof. exact (eq_refl term5). Qed.
Lemma lem1631046 : (term4 = term5) = (term5 = term5).
Proof. exact (MK_COMB (@lem1631044) (@lem1631045)). Qed.
Lemma lem1631048 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1631049 (x : real) : (x = x) = True.
Proof. exact (@lem1631048 real x). Qed.
Lemma lem1631050 : (term5 = term5) = True.
Proof. exact (@lem1631049 term5). Qed.
Lemma lem1631051 : (term4 = term5) = True.
Proof. exact (TRANS (@lem1631046) (@lem1631050)). Qed.
Lemma lem1631052 : True = (term4 = term5).
Proof. exact (SYM (@lem1631051)). Qed.
Lemma lem1631053 : term4 = term5.
Proof. exact (EQ_MP (@lem1631052) (@lem0)). Qed.
Lemma lem1631054 (x : real) : term31 x.
Proof. exact (@lem1338986 x). Qed.
Lemma lem1631055 (x : real) : (term31 x) = ((term32 x) = x).
Proof. exact (eq_refl (term31 x)). Qed.
Lemma lem1631057 (x : real) : term33 x.
Proof. exact (EQ_MP (@lem1344314 x) (@lem1344313 x)). Qed.
Lemma lem1631058 (x : real) (n : nat) : term34 x n.
Proof. exact (@lem1631057 x n). Qed.
Lemma lem1631059 (x : real) (n : nat) : (term34 x n) = ((term35 x n) = (term36 x n)).
Proof. exact (eq_refl (term34 x n)). Qed.
Lemma lem1631065 (x : real) (n : nat) : (term35 x n) = (term36 x n).
Proof. exact (EQ_MP (@lem1631059 x n) (@lem1631058 x n)). Qed.
Lemma lem1631066 (n : nat) : (term13 n) = (term37 n).
Proof. exact (@lem1631065 term5 n). Qed.
Lemma lem1631068 (x : real) : (term32 x) = x.
Proof. exact (EQ_MP (@lem1631055 x) (@lem1631054 x)). Qed.
Lemma lem1631069 (n : nat) : (term37 n) = (term9 n).
Proof. exact (@lem1631068 (term9 n)). Qed.
Lemma lem1631071 (n : nat) (h1 : (term9 n) = term5) : (term9 n) = term5.
Proof. exact (h1). Qed.
Lemma lem1631072 (n : nat) (h1 : (term9 n) = term5) : (term37 n) = term5.
Proof. exact (TRANS (@lem1631069 n) (@lem1631071 n h1)). Qed.
Lemma lem1631073 (n : nat) (h1 : (term9 n) = term5) : (term13 n) = term5.
Proof. exact (TRANS (@lem1631066 n) (@lem1631072 n h1)). Qed.
Lemma lem1631074 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1631075 (n : nat) (h1 : (term9 n) = term5) : (term38 n) = term30.
Proof. exact (MK_COMB (@lem1631074) (@lem1631073 n h1)). Qed.
Lemma lem1631076 : term5 = term5.
Proof. exact (eq_refl term5). Qed.
Lemma lem1631077 (n : nat) (h1 : (term9 n) = term5) : ((term13 n) = term5) = (term5 = term5).
Proof. exact (MK_COMB (@lem1631075 n h1) (@lem1631076)). Qed.
Lemma lem1631079 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1631080 (x : real) : (x = x) = True.
Proof. exact (@lem1631079 real x). Qed.
Lemma lem1631081 : (term5 = term5) = True.
Proof. exact (@lem1631080 term5). Qed.
Lemma lem1631082 (n : nat) (h1 : (term9 n) = term5) : ((term13 n) = term5) = True.
Proof. exact (TRANS (@lem1631077 n h1) (@lem1631081)). Qed.
Lemma lem1631083 (n : nat) (h1 : (term9 n) = term5) : True = ((term13 n) = term5).
Proof. exact (SYM (@lem1631082 n h1)). Qed.
Lemma lem1631084 (n : nat) (h1 : (term9 n) = term5) : (term13 n) = term5.
Proof. exact (EQ_MP (@lem1631083 n h1) (@lem0)). Qed.
Lemma lem1631085 (n : nat) : term15 n.
Proof. exact (fun h0 : (term9 n) = term5 => @lem1631084 n h0). Qed.
Lemma lem1631090 : term19.
Proof. exact (fun n : nat => @lem1631085 n). Qed.
Lemma lem1631091 : term21.
Proof. exact (conj (@lem1631053) (@lem1631090)). Qed.
Lemma lem1631092 : term26.
Proof. exact (@lem1631028 (@lem1631091)). Qed.
