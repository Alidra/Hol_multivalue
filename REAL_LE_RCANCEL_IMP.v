Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LE_RCANCEL_IMP_term_abbrevs.
Require Import REAL_LE_LCANCEL_IMP_spec.
Require Import thm0_spec.
Require Import thm1338712_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm7_spec.
Lemma lem1599020 (x : real) : term0 x.
Proof. exact (@lem1599019 x). Qed.
Lemma lem1599021 (x : real) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1599022 (x : real) : term1 x.
Proof. exact (EQ_MP (@lem1599021 x) (@lem1599020 x)). Qed.
Lemma lem1599023 (x : real) (y : real) : term2 x y.
Proof. exact (@lem1599022 x y). Qed.
Lemma lem1599024 (x : real) (y : real) : (term2 x y) = (term3 x y).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem1599025 (x : real) (y : real) : term3 x y.
Proof. exact (EQ_MP (@lem1599024 x y) (@lem1599023 x y)). Qed.
Lemma lem1599026 (x : real) (y : real) (z : real) : term4 x y z.
Proof. exact (@lem1599025 x y z). Qed.
Lemma lem1599027 (x : real) (y : real) (z : real) : (term4 x y z) = (term5 x y z).
Proof. exact (eq_refl (term4 x y z)). Qed.
Lemma lem1599028 (x : real) (y : real) (z : real) : term5 x y z.
Proof. exact (EQ_MP (@lem1599027 x y z) (@lem1599026 x y z)). Qed.
Lemma lem1599029 (x : real) (y : real) (z : real) : (term5 x y z) = ((term5 x y z) = True).
Proof. exact (@lem7 (term5 x y z)). Qed.
Lemma lem1599031 (x : real) : term6 x.
Proof. exact (@lem1338712 x). Qed.
Lemma lem1599032 (x : real) : (term6 x) = (term7 x).
Proof. exact (eq_refl (term6 x)). Qed.
Lemma lem1599033 (x : real) : term7 x.
Proof. exact (EQ_MP (@lem1599032 x) (@lem1599031 x)). Qed.
Lemma lem1599034 (x : real) (y : real) : term8 x y.
Proof. exact (@lem1599033 x y). Qed.
Lemma lem1599035 (y : real) (x : real) : (term8 x y) = ((real_mul x y) = (real_mul y x)).
Proof. exact (eq_refl (term8 x y)). Qed.
Lemma lem1599054 (y : real) (x : real) : (real_mul x y) = (real_mul y x).
Proof. exact (EQ_MP (@lem1599035 y x) (@lem1599034 x y)). Qed.
Lemma lem1599055 (z : real) (x : real) : (real_mul x z) = (real_mul z x).
Proof. exact (@lem1599054 z x). Qed.
Lemma lem1599056 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem1599057 (z : real) (x : real) : (term9 x z) = (term9 z x).
Proof. exact (MK_COMB (@lem1599056) (@lem1599055 z x)). Qed.
Lemma lem1599059 (y : real) (x : real) : (real_mul x y) = (real_mul y x).
Proof. exact (EQ_MP (@lem1599035 y x) (@lem1599034 x y)). Qed.
Lemma lem1599060 (z : real) (y : real) : (real_mul y z) = (real_mul z y).
Proof. exact (@lem1599059 z y). Qed.
Lemma lem1599061 (x : real) (z : real) (y : real) : (term10 x y z) = (term11 x z y).
Proof. exact (MK_COMB (@lem1599057 z x) (@lem1599060 z y)). Qed.
Lemma lem1599062 (z : real) : (term12 z) = (term12 z).
Proof. exact (eq_refl (term12 z)). Qed.
Lemma lem1599063 (x : real) (z : real) (y : real) : (term13 x y z) = (term14 x z y).
Proof. exact (MK_COMB (@lem1599062 z) (@lem1599061 x z y)). Qed.
Lemma lem1599064 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1599065 (x : real) (z : real) (y : real) : (term15 x y z) = (term16 x z y).
Proof. exact (MK_COMB (@lem1599064) (@lem1599063 x z y)). Qed.
Lemma lem1599066 (x : real) (y : real) : (real_le x y) = (real_le x y).
Proof. exact (eq_refl (real_le x y)). Qed.
Lemma lem1599067 (z : real) (x : real) (y : real) : (term17 z x y) = (term5 z x y).
Proof. exact (MK_COMB (@lem1599065 x z y) (@lem1599066 x y)). Qed.
Lemma lem1599068 (x : real) (y : real) : (term18 x y) = (term19 x y).
Proof. exact (fun_ext (fun z : real => @lem1599067 z x y)). Qed.
Lemma lem1599069 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1599070 (x : real) (y : real) : (term20 x y) = (term21 x y).
Proof. exact (MK_COMB (@lem1599069) (@lem1599068 x y)). Qed.
Lemma lem1599071 (x : real) : (term22 x) = (term23 x).
Proof. exact (fun_ext (fun y : real => @lem1599070 x y)). Qed.
Lemma lem1599072 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1599073 (x : real) : (term24 x) = (term25 x).
Proof. exact (MK_COMB (@lem1599072) (@lem1599071 x)). Qed.
Lemma lem1599074 : term26 = term27.
Proof. exact (fun_ext (fun x : real => @lem1599073 x)). Qed.
Lemma lem1599075 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1599076 : term28 = term29.
Proof. exact (MK_COMB (@lem1599075) (@lem1599074)). Qed.
Lemma lem1599077 : term29 = term28.
Proof. exact (SYM (@lem1599076)). Qed.
Lemma lem1599091 (x : real) (y : real) (z : real) : (term5 x y z) = True.
Proof. exact (EQ_MP (@lem1599029 x y z) (@lem1599028 x y z)). Qed.
Lemma lem1599092 (z : real) (x : real) (y : real) : (term5 z x y) = True.
Proof. exact (@lem1599091 z x y). Qed.
Lemma lem1599093 (x : real) (y : real) : (term19 x y) = term30.
Proof. exact (fun_ext (fun z : real => @lem1599092 z x y)). Qed.
Lemma lem1599094 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1599095 (x : real) (y : real) : (term21 x y) = term31.
Proof. exact (MK_COMB (@lem1599094) (@lem1599093 x y)). Qed.
Lemma lem1599097 {A : Type'} (t : Prop) : (term32 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1599098 (t : Prop) : (term33 t) = t.
Proof. exact (@lem1599097 real t). Qed.
Lemma lem1599099 : term31 = True.
Proof. exact (@lem1599098 True). Qed.
Lemma lem1599100 (x : real) (y : real) : (term21 x y) = True.
Proof. exact (TRANS (@lem1599095 x y) (@lem1599099)). Qed.
Lemma lem1599101 (x : real) : (term23 x) = term30.
Proof. exact (fun_ext (fun y : real => @lem1599100 x y)). Qed.
Lemma lem1599102 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1599103 (x : real) : (term25 x) = term31.
Proof. exact (MK_COMB (@lem1599102) (@lem1599101 x)). Qed.
Lemma lem1599105 {A : Type'} (t : Prop) : (term32 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1599106 (t : Prop) : (term33 t) = t.
Proof. exact (@lem1599105 real t). Qed.
Lemma lem1599107 : term31 = True.
Proof. exact (@lem1599106 True). Qed.
Lemma lem1599108 (x : real) : (term25 x) = True.
Proof. exact (TRANS (@lem1599103 x) (@lem1599107)). Qed.
Lemma lem1599109 : term27 = term30.
Proof. exact (fun_ext (fun x : real => @lem1599108 x)). Qed.
Lemma lem1599110 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1599111 : term29 = term31.
Proof. exact (MK_COMB (@lem1599110) (@lem1599109)). Qed.
Lemma lem1599113 {A : Type'} (t : Prop) : (term32 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1599114 (t : Prop) : (term33 t) = t.
Proof. exact (@lem1599113 real t). Qed.
Lemma lem1599115 : term31 = True.
Proof. exact (@lem1599114 True). Qed.
Lemma lem1599116 : term29 = True.
Proof. exact (TRANS (@lem1599111) (@lem1599115)). Qed.
Lemma lem1599117 : True = term29.
Proof. exact (SYM (@lem1599116)). Qed.
Lemma lem1599118 : term29.
Proof. exact (EQ_MP (@lem1599117) (@lem0)). Qed.
Lemma lem1599119 : term28.
Proof. exact (EQ_MP (@lem1599077) (@lem1599118)). Qed.
