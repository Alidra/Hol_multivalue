Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_DIV_RMUL_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import REAL_MUL_RID_spec.
Require Import real_div_spec.
Require Import thm0_spec.
Require Import thm1338912_spec.
Require Import thm1340174_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4211_spec.
Require Import thm82_spec.
Lemma lem1593007 (x : real) (y : real) (z : real) (h1 : (term0 x y z) = (term1 x y z)) : (term0 x y z) = (term1 x y z).
Proof. exact (h1). Qed.
Lemma lem1593008 (x : real) (y : real) (z : real) (h1 : (term0 x y z) = (term1 x y z)) : (term1 x y z) = (term0 x y z).
Proof. exact (SYM (@lem1593007 x y z h1)). Qed.
Lemma lem1593009 (x : real) (y : real) (z : real) (h1 : (term1 x y z) = (term0 x y z)) : (term1 x y z) = (term0 x y z).
Proof. exact (h1). Qed.
Lemma lem1593010 (x : real) (y : real) (z : real) (h1 : (term1 x y z) = (term0 x y z)) : (term0 x y z) = (term1 x y z).
Proof. exact (SYM (@lem1593009 x y z h1)). Qed.
Lemma lem1593011 (x : real) (y : real) (z : real) : ((term0 x y z) = (term1 x y z)) = ((term1 x y z) = (term0 x y z)).
Proof. exact (prop_ext (fun h1 : (term0 x y z) = (term1 x y z) => @lem1593008 x y z h1) (fun h1 : (term1 x y z) = (term0 x y z) => @lem1593010 x y z h1)). Qed.
Lemma lem1593012 (x : real) (y : real) : (term2 x y) = (term3 x y).
Proof. exact (fun_ext (fun z : real => @lem1593011 x y z)). Qed.
Lemma lem1593013 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1593014 (x : real) (y : real) : (term4 x y) = (term5 x y).
Proof. exact (MK_COMB (@lem1593013) (@lem1593012 x y)). Qed.
Lemma lem1593015 (x : real) : (term6 x) = (term7 x).
Proof. exact (fun_ext (fun y : real => @lem1593014 x y)). Qed.
Lemma lem1593016 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1593017 (x : real) : (term8 x) = (term9 x).
Proof. exact (MK_COMB (@lem1593016) (@lem1593015 x)). Qed.
Lemma lem1593018 : term10 = term11.
Proof. exact (fun_ext (fun x : real => @lem1593017 x)). Qed.
Lemma lem1593019 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1593020 : term12 = term13.
Proof. exact (MK_COMB (@lem1593019) (@lem1593018)). Qed.
Lemma lem1593021 : term13.
Proof. exact (EQ_MP (@lem1593020) (@lem1338912)). Qed.
Lemma lem1593022 (x : real) : term14 x.
Proof. exact (@lem1383409 x). Qed.
Lemma lem1593023 (x : real) : (term14 x) = ((term15 x) = x).
Proof. exact (eq_refl (term14 x)). Qed.
Lemma lem1593025 (x : real) : term16 x.
Proof. exact (@lem1340174 x). Qed.
Lemma lem1593026 (x : real) : (term16 x) = (term17 x).
Proof. exact (eq_refl (term16 x)). Qed.
Lemma lem1593027 (x : real) : term17 x.
Proof. exact (EQ_MP (@lem1593026 x) (@lem1593025 x)). Qed.
Lemma lem1593028 (x : real) (h1 : term18 x) : term18 x.
Proof. exact (h1). Qed.
Lemma lem1593029 (x : real) (h1 : term18 x) : (term19 x) = term20.
Proof. exact (@lem1593027 x (@lem1593028 x h1)). Qed.
Lemma lem1593035 (x : real) : term21 x.
Proof. exact (@lem1593021 x). Qed.
Lemma lem1593036 (x : real) : (term21 x) = (term9 x).
Proof. exact (eq_refl (term21 x)). Qed.
Lemma lem1593037 (x : real) : term9 x.
Proof. exact (EQ_MP (@lem1593036 x) (@lem1593035 x)). Qed.
Lemma lem1593038 (x : real) (y : real) : term22 x y.
Proof. exact (@lem1593037 x y). Qed.
Lemma lem1593039 (x : real) (y : real) : (term22 x y) = (term5 x y).
Proof. exact (eq_refl (term22 x y)). Qed.
Lemma lem1593040 (x : real) (y : real) : term5 x y.
Proof. exact (EQ_MP (@lem1593039 x y) (@lem1593038 x y)). Qed.
Lemma lem1593041 (x : real) (y : real) (z : real) : term23 x y z.
Proof. exact (@lem1593040 x y z). Qed.
Lemma lem1593042 (x : real) (y : real) (z : real) : (term23 x y z) = ((term1 x y z) = (term0 x y z)).
Proof. exact (eq_refl (term23 x y z)). Qed.
Lemma lem1593044 (x : real) : term24 x.
Proof. exact (@lem1344936 x). Qed.
Lemma lem1593045 (x : real) : (term24 x) = (term25 x).
Proof. exact (eq_refl (term24 x)). Qed.
Lemma lem1593046 (x : real) : term25 x.
Proof. exact (EQ_MP (@lem1593045 x) (@lem1593044 x)). Qed.
Lemma lem1593047 (x : real) (y : real) : term26 x y.
Proof. exact (@lem1593046 x y). Qed.
Lemma lem1593048 (x : real) (y : real) : (term26 x y) = ((real_div x y) = (term27 x y)).
Proof. exact (eq_refl (term26 x y)). Qed.
Lemma lem1593061 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term28 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem1593062 (p : Prop) (q : Prop) (p' : Prop) : term29 p q p'.
Proof. exact (fun q' : Prop => @lem1593061 p q p' q'). Qed.
Lemma lem1593063 (p : Prop) (q : Prop) : term30 p q.
Proof. exact (fun p' : Prop => @lem1593062 p q p'). Qed.
Lemma lem1593064 (y : real) (x : real) : term31 y x.
Proof. exact (@lem1593063 (term18 y) ((term32 x y) = x)). Qed.
Lemma lem1593065 (y : real) (x : real) (p' : Prop) : term33 y x p'.
Proof. exact (@lem1593064 y x p'). Qed.
Lemma lem1593066 (y : real) (x : real) (p' : Prop) : (term33 y x p') = (term34 y x p').
Proof. exact (eq_refl (term33 y x p')). Qed.
Lemma lem1593067 (y : real) (x : real) (p' : Prop) : term34 y x p'.
Proof. exact (EQ_MP (@lem1593066 y x p') (@lem1593065 y x p')). Qed.
Lemma lem1593068 (y : real) (x : real) (p' : Prop) (q' : Prop) : term35 y x p' q'.
Proof. exact (@lem1593067 y x p' q'). Qed.
Lemma lem1593069 (y : real) (x : real) (p' : Prop) (q' : Prop) : (term35 y x p' q') = (term36 y x p' q').
Proof. exact (eq_refl (term35 y x p' q')). Qed.
Lemma lem1593070 (y : real) (x : real) (p' : Prop) (q' : Prop) : term36 y x p' q'.
Proof. exact (EQ_MP (@lem1593069 y x p' q') (@lem1593068 y x p' q')). Qed.
Lemma lem1593073 (y : real) : (term18 y) = (term18 y).
Proof. exact (eq_refl (term18 y)). Qed.
Lemma lem1593074 (x : real) (y : real) (q' : Prop) : term37 x y q'.
Proof. exact (@lem1593070 y x (term18 y) q'). Qed.
Lemma lem1593075 (x : real) (y : real) (q' : Prop) : term38 x y q'.
Proof. exact (@lem1593074 x y q' (@lem1593073 y)). Qed.
Lemma lem1593076 (y : real) (h1 : term18 y) : term18 y.
Proof. exact (h1). Qed.
Lemma lem1593077 (y : real) : term39 y.
Proof. exact (@lem82 (y = term40)). Qed.
Lemma lem1593093 (x : real) (y : real) : (real_div x y) = (term27 x y).
Proof. exact (EQ_MP (@lem1593048 x y) (@lem1593047 x y)). Qed.
Lemma lem1593094 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1593095 (x : real) (y : real) : (term41 x y) = (term42 x y).
Proof. exact (MK_COMB (@lem1593094) (@lem1593093 x y)). Qed.
Lemma lem1593096 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1593097 (x : real) (y : real) : (term32 x y) = (term43 x y).
Proof. exact (MK_COMB (@lem1593095 x y) (@lem1593096 y)). Qed.
Lemma lem1593099 (x : real) (y : real) (z : real) : (term1 x y z) = (term0 x y z).
Proof. exact (EQ_MP (@lem1593042 x y z) (@lem1593041 x y z)). Qed.
Lemma lem1593100 (x : real) (y : real) : (term43 x y) = (term44 x y).
Proof. exact (@lem1593099 x (real_inv y) y). Qed.
Lemma lem1593102 (x : real) : term17 x.
Proof. exact (fun h0 : term18 x => @lem1593029 x h0). Qed.
Lemma lem1593103 (y : real) : term17 y.
Proof. exact (@lem1593102 y). Qed.
Lemma lem1593105 (y : real) (h1 : term18 y) : (y = term40) = False.
Proof. exact (@lem1593077 y (@lem1593076 y h1)). Qed.
Lemma lem1593106 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1593107 (y : real) (h1 : term18 y) : (term18 y) = (~ False).
Proof. exact (MK_COMB (@lem1593106) (@lem1593105 y h1)). Qed.
Lemma lem1593109 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1593110 (y : real) (h1 : term18 y) : (term18 y) = True.
Proof. exact (TRANS (@lem1593107 y h1) (@lem1593109)). Qed.
Lemma lem1593111 (y : real) (h1 : term18 y) : True = (term18 y).
Proof. exact (SYM (@lem1593110 y h1)). Qed.
Lemma lem1593112 (y : real) (h1 : term18 y) : term18 y.
Proof. exact (EQ_MP (@lem1593111 y h1) (@lem0)). Qed.
Lemma lem1593113 (y : real) (h1 : term18 y) : (term19 y) = term20.
Proof. exact (@lem1593103 y (@lem1593112 y h1)). Qed.
Lemma lem1593114 (x : real) : (real_mul x) = (real_mul x).
Proof. exact (eq_refl (real_mul x)). Qed.
Lemma lem1593115 (x : real) (y : real) (h1 : term18 y) : (term44 x y) = (term15 x).
Proof. exact (MK_COMB (@lem1593114 x) (@lem1593113 y h1)). Qed.
Lemma lem1593117 (x : real) : (term15 x) = x.
Proof. exact (EQ_MP (@lem1593023 x) (@lem1593022 x)). Qed.
Lemma lem1593118 (x : real) (y : real) (h1 : term18 y) : (term44 x y) = x.
Proof. exact (TRANS (@lem1593115 x y h1) (@lem1593117 x)). Qed.
Lemma lem1593119 (x : real) (y : real) (h1 : term18 y) : (term43 x y) = x.
Proof. exact (TRANS (@lem1593100 x y) (@lem1593118 x y h1)). Qed.
Lemma lem1593120 (x : real) (y : real) (h1 : term18 y) : (term32 x y) = x.
Proof. exact (TRANS (@lem1593097 x y) (@lem1593119 x y h1)). Qed.
Lemma lem1593121 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1593122 (x : real) (y : real) (h1 : term18 y) : (term45 x y) = (@eq real x).
Proof. exact (MK_COMB (@lem1593121) (@lem1593120 x y h1)). Qed.
Lemma lem1593123 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1593124 (x : real) (y : real) (h1 : term18 y) : ((term32 x y) = x) = (x = x).
Proof. exact (MK_COMB (@lem1593122 x y h1) (@lem1593123 x)). Qed.
Lemma lem1593126 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1593127 (x : real) : (x = x) = True.
Proof. exact (@lem1593126 real x). Qed.
Lemma lem1593128 (x : real) (y : real) (h1 : term18 y) : ((term32 x y) = x) = True.
Proof. exact (TRANS (@lem1593124 x y h1) (@lem1593127 x)). Qed.
Lemma lem1593129 (y : real) (x : real) : term46 y x.
Proof. exact (fun h0 : term18 y => @lem1593128 x y h0). Qed.
Lemma lem1593130 (x : real) (y : real) : term47 x y.
Proof. exact (@lem1593075 x y True). Qed.
Lemma lem1593131 (x : real) (y : real) : (term48 y x) = (term49 y).
Proof. exact (@lem1593130 x y (@lem1593129 y x)). Qed.
Lemma lem1593133 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem1593134 (y : real) : (term49 y) = True.
Proof. exact (@lem1593133 (term18 y)). Qed.
Lemma lem1593135 (y : real) (x : real) : (term48 y x) = True.
Proof. exact (TRANS (@lem1593131 x y) (@lem1593134 y)). Qed.
Lemma lem1593136 (x : real) : (term50 x) = term51.
Proof. exact (fun_ext (fun y : real => @lem1593135 y x)). Qed.
Lemma lem1593137 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1593138 (x : real) : (term52 x) = term53.
Proof. exact (MK_COMB (@lem1593137) (@lem1593136 x)). Qed.
Lemma lem1593140 {A : Type'} (t : Prop) : (term54 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1593141 (t : Prop) : (term55 t) = t.
Proof. exact (@lem1593140 real t). Qed.
Lemma lem1593142 : term53 = True.
Proof. exact (@lem1593141 True). Qed.
Lemma lem1593143 (x : real) : (term52 x) = True.
Proof. exact (TRANS (@lem1593138 x) (@lem1593142)). Qed.
Lemma lem1593144 : term56 = term51.
Proof. exact (fun_ext (fun x : real => @lem1593143 x)). Qed.
Lemma lem1593145 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1593146 : term57 = term53.
Proof. exact (MK_COMB (@lem1593145) (@lem1593144)). Qed.
Lemma lem1593148 {A : Type'} (t : Prop) : (term54 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1593149 (t : Prop) : (term55 t) = t.
Proof. exact (@lem1593148 real t). Qed.
Lemma lem1593150 : term53 = True.
Proof. exact (@lem1593149 True). Qed.
Lemma lem1593151 : term57 = True.
Proof. exact (TRANS (@lem1593146) (@lem1593150)). Qed.
Lemma lem1593152 : True = term57.
Proof. exact (SYM (@lem1593151)). Qed.
Lemma lem1593153 : term57.
Proof. exact (EQ_MP (@lem1593152) (@lem0)). Qed.
