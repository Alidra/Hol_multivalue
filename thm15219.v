Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm15219_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm12653_spec.
Require Import thm14834_spec.
Require Import thm1820_spec.
Require Import thm1822_spec.
Require Import thm1823_spec.
Require Import thm1857_spec.
Lemma lem15001 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem15002 (g' : Prop) : (False = g') = (~ g').
Proof. exact (@lem15001 g'). Qed.
Lemma lem15003 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem15004 (g' : Prop) : (term0 g') = (term1 g').
Proof. exact (MK_COMB (@lem15003) (@lem15002 g')). Qed.
Lemma lem15020 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem15021 {_2963 : Type'} (t1 : _2963) (t2 : _2963) : (@COND _2963 False t1 t2) = t2.
Proof. exact (@lem15020 _2963 t1 t2). Qed.
Lemma lem15022 {_2963 : Type'} (t : _2963) (e : _2963) : (@COND _2963 False t e) = e.
Proof. exact (@lem15021 _2963 t e). Qed.
Lemma lem15023 {_2963 : Type'} : (@eq _2963) = (@eq _2963).
Proof. exact (eq_refl (@eq _2963)). Qed.
Lemma lem15024 {_2963 : Type'} (t : _2963) (e : _2963) : (term2 _2963 t e) = (@eq _2963 e).
Proof. exact (MK_COMB (@lem15023 _2963) (@lem15022 _2963 t e)). Qed.
Lemma lem15025 {_2963 : Type'} (g' : Prop) (t' : _2963) (e' : _2963) : (@COND _2963 g' t' e') = (@COND _2963 g' t' e').
Proof. exact (eq_refl (@COND _2963 g' t' e')). Qed.
Lemma lem15026 {_2963 : Type'} (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : ((@COND _2963 False t e) = (@COND _2963 g' t' e')) = (e = (@COND _2963 g' t' e')).
Proof. exact (MK_COMB (@lem15024 _2963 t e) (@lem15025 _2963 g' t' e')). Qed.
Lemma lem15029 {_2963 : Type'} (g' : Prop) (e : _2963) (e' : _2963) : (term3 _2963 g' e e') = (term3 _2963 g' e e').
Proof. exact (eq_refl (term3 _2963 g' e e')). Qed.
Lemma lem15030 {_2963 : Type'} (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : (term4 _2963 t e g' t' e') = (term5 _2963 e g' t' e').
Proof. exact (MK_COMB (@lem15029 _2963 g' e e') (@lem15026 _2963 t e g' t' e')). Qed.
Lemma lem15033 {_2963 : Type'} (g' : Prop) (t : _2963) (t' : _2963) : (term6 _2963 g' t t') = (term6 _2963 g' t t').
Proof. exact (eq_refl (term6 _2963 g' t t')). Qed.
Lemma lem15034 {_2963 : Type'} (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : (term7 _2963 t e g' t' e') = (term8 _2963 t e g' t' e').
Proof. exact (MK_COMB (@lem15033 _2963 g' t t') (@lem15030 _2963 t e g' t' e')). Qed.
Lemma lem15037 {_2963 : Type'} (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : (term9 _2963 t e g' t' e') = (term10 _2963 t e g' t' e').
Proof. exact (MK_COMB (@lem15004 g') (@lem15034 _2963 t e g' t' e')). Qed.
Lemma lem15040 {_2963 : Type'} (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : (term10 _2963 t e g' t' e') = (term9 _2963 t e g' t' e').
Proof. exact (SYM (@lem15037 _2963 t e g' t' e')). Qed.
Lemma lem15041 (g' : Prop) : term11 g'.
Proof. exact (@lem9851 g'). Qed.
Lemma lem15042 (g' : Prop) : (term11 g') = (term12 g').
Proof. exact (eq_refl (term11 g')). Qed.
Lemma lem15043 (g' : Prop) : term12 g'.
Proof. exact (EQ_MP (@lem15042 g') (@lem15041 g')). Qed.
Lemma lem15044 (g' : Prop) (h1 : g' = True) : g' = True.
Proof. exact (h1). Qed.
Lemma lem15045 (g' : Prop) (h1 : g' = False) : g' = False.
Proof. exact (h1). Qed.
Lemma lem15064 {_2963 : Type'} (t : _2963) (e : _2963) (t' : _2963) (e' : _2963) : (term13 _2963 t e t' e') = (term13 _2963 t e t' e').
Proof. exact (eq_refl (term13 _2963 t e t' e')). Qed.
Lemma lem15065 {_2963 : Type'} (t : _2963) (e : _2963) (t' : _2963) (e' : _2963) (g' : Prop) (h1 : g' = True) : (term14 _2963 t e t' e' g') = (term15 _2963 t e t' e').
Proof. exact (MK_COMB (@lem15064 _2963 t e t' e') (@lem15044 g' h1)). Qed.
Lemma lem15066 {_2963 : Type'} (t : _2963) (e : _2963) (t' : _2963) (e' : _2963) : (term15 _2963 t e t' e') = (term16 _2963 t e t' e').
Proof. exact (eq_refl (term15 _2963 t e t' e')). Qed.
Lemma lem15067 {_2963 : Type'} (t : _2963) (e : _2963) (t' : _2963) (e' : _2963) (g' : Prop) : (term17 _2963 t e t' e' g') = (term17 _2963 t e t' e' g').
Proof. exact (eq_refl (term17 _2963 t e t' e' g')). Qed.
Lemma lem15068 {_2963 : Type'} (g' : Prop) (t : _2963) (e : _2963) (t' : _2963) (e' : _2963) : ((term14 _2963 t e t' e' g') = (term15 _2963 t e t' e')) = ((term14 _2963 t e t' e' g') = (term16 _2963 t e t' e')).
Proof. exact (MK_COMB (@lem15067 _2963 t e t' e' g') (@lem15066 _2963 t e t' e')). Qed.
Lemma lem15069 {_2963 : Type'} (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : (term14 _2963 t e t' e' g') = (term10 _2963 t e g' t' e').
Proof. exact (eq_refl (term14 _2963 t e t' e' g')). Qed.
Lemma lem15070 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem15071 {_2963 : Type'} (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : (term17 _2963 t e t' e' g') = (term18 _2963 t e g' t' e').
Proof. exact (MK_COMB (@lem15070) (@lem15069 _2963 t e g' t' e')). Qed.
Lemma lem15072 {_2963 : Type'} (t : _2963) (e : _2963) (t' : _2963) (e' : _2963) : (term16 _2963 t e t' e') = (term16 _2963 t e t' e').
Proof. exact (eq_refl (term16 _2963 t e t' e')). Qed.
Lemma lem15073 {_2963 : Type'} (g' : Prop) (t : _2963) (e : _2963) (t' : _2963) (e' : _2963) : ((term14 _2963 t e t' e' g') = (term16 _2963 t e t' e')) = ((term10 _2963 t e g' t' e') = (term16 _2963 t e t' e')).
Proof. exact (MK_COMB (@lem15071 _2963 t e g' t' e') (@lem15072 _2963 t e t' e')). Qed.
Lemma lem15074 {_2963 : Type'} (g' : Prop) (t : _2963) (e : _2963) (t' : _2963) (e' : _2963) : ((term14 _2963 t e t' e' g') = (term15 _2963 t e t' e')) = ((term10 _2963 t e g' t' e') = (term16 _2963 t e t' e')).
Proof. exact (TRANS (@lem15068 _2963 g' t e t' e') (@lem15073 _2963 g' t e t' e')). Qed.
Lemma lem15075 {_2963 : Type'} (t : _2963) (e : _2963) (t' : _2963) (e' : _2963) (g' : Prop) (h1 : g' = True) : (term10 _2963 t e g' t' e') = (term16 _2963 t e t' e').
Proof. exact (EQ_MP (@lem15074 _2963 g' t e t' e') (@lem15065 _2963 t e t' e' g' h1)). Qed.
Lemma lem15076 {_2963 : Type'} (t : _2963) (e : _2963) (t' : _2963) (e' : _2963) (g' : Prop) (h1 : g' = True) : (term16 _2963 t e t' e') = (term10 _2963 t e g' t' e').
Proof. exact (SYM (@lem15075 _2963 t e t' e' g' h1)). Qed.
Lemma lem15077 {_2963 : Type'} (t : _2963) (e : _2963) (t' : _2963) (e' : _2963) : (term13 _2963 t e t' e') = (term13 _2963 t e t' e').
Proof. exact (eq_refl (term13 _2963 t e t' e')). Qed.
Lemma lem15078 {_2963 : Type'} (t : _2963) (e : _2963) (t' : _2963) (e' : _2963) (g' : Prop) (h1 : g' = False) : (term14 _2963 t e t' e' g') = (term19 _2963 t e t' e').
Proof. exact (MK_COMB (@lem15077 _2963 t e t' e') (@lem15045 g' h1)). Qed.
Lemma lem15079 {_2963 : Type'} (t : _2963) (e : _2963) (t' : _2963) (e' : _2963) : (term19 _2963 t e t' e') = (term20 _2963 t e t' e').
Proof. exact (eq_refl (term19 _2963 t e t' e')). Qed.
Lemma lem15080 {_2963 : Type'} (t : _2963) (e : _2963) (t' : _2963) (e' : _2963) (g' : Prop) : (term17 _2963 t e t' e' g') = (term17 _2963 t e t' e' g').
Proof. exact (eq_refl (term17 _2963 t e t' e' g')). Qed.
Lemma lem15081 {_2963 : Type'} (g' : Prop) (t : _2963) (e : _2963) (t' : _2963) (e' : _2963) : ((term14 _2963 t e t' e' g') = (term19 _2963 t e t' e')) = ((term14 _2963 t e t' e' g') = (term20 _2963 t e t' e')).
Proof. exact (MK_COMB (@lem15080 _2963 t e t' e' g') (@lem15079 _2963 t e t' e')). Qed.
Lemma lem15082 {_2963 : Type'} (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : (term14 _2963 t e t' e' g') = (term10 _2963 t e g' t' e').
Proof. exact (eq_refl (term14 _2963 t e t' e' g')). Qed.
Lemma lem15083 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem15084 {_2963 : Type'} (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : (term17 _2963 t e t' e' g') = (term18 _2963 t e g' t' e').
Proof. exact (MK_COMB (@lem15083) (@lem15082 _2963 t e g' t' e')). Qed.
Lemma lem15085 {_2963 : Type'} (t : _2963) (e : _2963) (t' : _2963) (e' : _2963) : (term20 _2963 t e t' e') = (term20 _2963 t e t' e').
Proof. exact (eq_refl (term20 _2963 t e t' e')). Qed.
Lemma lem15086 {_2963 : Type'} (g' : Prop) (t : _2963) (e : _2963) (t' : _2963) (e' : _2963) : ((term14 _2963 t e t' e' g') = (term20 _2963 t e t' e')) = ((term10 _2963 t e g' t' e') = (term20 _2963 t e t' e')).
Proof. exact (MK_COMB (@lem15084 _2963 t e g' t' e') (@lem15085 _2963 t e t' e')). Qed.
Lemma lem15087 {_2963 : Type'} (g' : Prop) (t : _2963) (e : _2963) (t' : _2963) (e' : _2963) : ((term14 _2963 t e t' e' g') = (term19 _2963 t e t' e')) = ((term10 _2963 t e g' t' e') = (term20 _2963 t e t' e')).
Proof. exact (TRANS (@lem15081 _2963 g' t e t' e') (@lem15086 _2963 g' t e t' e')). Qed.
Lemma lem15088 {_2963 : Type'} (t : _2963) (e : _2963) (t' : _2963) (e' : _2963) (g' : Prop) (h1 : g' = False) : (term10 _2963 t e g' t' e') = (term20 _2963 t e t' e').
Proof. exact (EQ_MP (@lem15087 _2963 g' t e t' e') (@lem15078 _2963 t e t' e' g' h1)). Qed.
Lemma lem15089 {_2963 : Type'} (t : _2963) (e : _2963) (t' : _2963) (e' : _2963) (g' : Prop) (h1 : g' = False) : (term20 _2963 t e t' e') = (term10 _2963 t e g' t' e').
Proof. exact (SYM (@lem15088 _2963 t e t' e' g' h1)). Qed.
Lemma lem15093 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem15094 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem15095 : term21 = (imp False).
Proof. exact (MK_COMB (@lem15094) (@lem15093)). Qed.
Lemma lem15099 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem15100 {_2963 : Type'} (t : _2963) (t' : _2963) : (term22 _2963 t t') = (t = t').
Proof. exact (@lem15099 (t = t')). Qed.
Lemma lem15103 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem15104 {_2963 : Type'} (t : _2963) (t' : _2963) : (term23 _2963 t t') = (term24 _2963 t t').
Proof. exact (MK_COMB (@lem15103) (@lem15100 _2963 t t')). Qed.
Lemma lem15110 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem15111 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem15112 : term21 = (imp False).
Proof. exact (MK_COMB (@lem15111) (@lem15110)). Qed.
Lemma lem15115 {_2963 : Type'} (e : _2963) (e' : _2963) : (e = e') = (e = e').
Proof. exact (eq_refl (e = e')). Qed.
Lemma lem15116 {_2963 : Type'} (e : _2963) (e' : _2963) : (term25 _2963 e e') = (term26 _2963 e e').
Proof. exact (MK_COMB (@lem15112) (@lem15115 _2963 e e')). Qed.
Lemma lem15118 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem15119 {_2963 : Type'} (e : _2963) (e' : _2963) : (term26 _2963 e e') = True.
Proof. exact (@lem15118 (e = e')). Qed.
Lemma lem15120 {_2963 : Type'} (e : _2963) (e' : _2963) : (term25 _2963 e e') = True.
Proof. exact (TRANS (@lem15116 _2963 e e') (@lem15119 _2963 e e')). Qed.
Lemma lem15121 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem15122 {_2963 : Type'} (e : _2963) (e' : _2963) : (term27 _2963 e e') = (imp True).
Proof. exact (MK_COMB (@lem15121) (@lem15120 _2963 e e')). Qed.
Lemma lem15126 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem15127 {_2963 : Type'} (t2 : _2963) (t1 : _2963) : (@COND _2963 True t1 t2) = t1.
Proof. exact (@lem15126 _2963 t2 t1). Qed.
Lemma lem15128 {_2963 : Type'} (e' : _2963) (t' : _2963) : (@COND _2963 True t' e') = t'.
Proof. exact (@lem15127 _2963 e' t'). Qed.
Lemma lem15129 {_2963 : Type'} (e : _2963) : (@eq _2963 e) = (@eq _2963 e).
Proof. exact (eq_refl (@eq _2963 e)). Qed.
Lemma lem15130 {_2963 : Type'} (e' : _2963) (e : _2963) (t' : _2963) : (e = (@COND _2963 True t' e')) = (e = t').
Proof. exact (MK_COMB (@lem15129 _2963 e) (@lem15128 _2963 e' t')). Qed.
Lemma lem15133 {_2963 : Type'} (e' : _2963) (e : _2963) (t' : _2963) : (term28 _2963 e t' e') = (term22 _2963 e t').
Proof. exact (MK_COMB (@lem15122 _2963 e e') (@lem15130 _2963 e' e t')). Qed.
Lemma lem15135 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem15136 {_2963 : Type'} (e : _2963) (t' : _2963) : (term22 _2963 e t') = (e = t').
Proof. exact (@lem15135 (e = t')). Qed.
Lemma lem15139 {_2963 : Type'} (e' : _2963) (e : _2963) (t' : _2963) : (term28 _2963 e t' e') = (e = t').
Proof. exact (TRANS (@lem15133 _2963 e' e t') (@lem15136 _2963 e t')). Qed.
Lemma lem15140 {_2963 : Type'} (e' : _2963) (t : _2963) (e : _2963) (t' : _2963) : (term29 _2963 t e t' e') = (term30 _2963 t e t').
Proof. exact (MK_COMB (@lem15104 _2963 t t') (@lem15139 _2963 e' e t')). Qed.
Lemma lem15145 {_2963 : Type'} (e' : _2963) (t : _2963) (e : _2963) (t' : _2963) : (term16 _2963 t e t' e') = (term31 _2963 t e t').
Proof. exact (MK_COMB (@lem15095) (@lem15140 _2963 e' t e t')). Qed.
Lemma lem15147 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem15148 {_2963 : Type'} (t : _2963) (e : _2963) (t' : _2963) : (term31 _2963 t e t') = True.
Proof. exact (@lem15147 (term30 _2963 t e t')). Qed.
Lemma lem15149 {_2963 : Type'} (t : _2963) (e : _2963) (t' : _2963) (e' : _2963) : (term16 _2963 t e t' e') = True.
Proof. exact (TRANS (@lem15145 _2963 e' t e t') (@lem15148 _2963 t e t')). Qed.
Lemma lem15150 {_2963 : Type'} (t : _2963) (e : _2963) (t' : _2963) (e' : _2963) : True = (term16 _2963 t e t' e').
Proof. exact (SYM (@lem15149 _2963 t e t' e')). Qed.
Lemma lem15151 {_2963 : Type'} (t : _2963) (e : _2963) (t' : _2963) (e' : _2963) : term16 _2963 t e t' e'.
Proof. exact (EQ_MP (@lem15150 _2963 t e t' e') (@lem0)). Qed.
Lemma lem15155 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem15156 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem15157 : term32 = (imp True).
Proof. exact (MK_COMB (@lem15156) (@lem15155)). Qed.
Lemma lem15161 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem15162 {_2963 : Type'} (t : _2963) (t' : _2963) : (term26 _2963 t t') = True.
Proof. exact (@lem15161 (t = t')). Qed.
Lemma lem15163 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem15164 {_2963 : Type'} (t : _2963) (t' : _2963) : (term33 _2963 t t') = (imp True).
Proof. exact (MK_COMB (@lem15163) (@lem15162 _2963 t t')). Qed.
Lemma lem15170 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem15171 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem15172 : term32 = (imp True).
Proof. exact (MK_COMB (@lem15171) (@lem15170)). Qed.
Lemma lem15175 {_2963 : Type'} (e : _2963) (e' : _2963) : (e = e') = (e = e').
Proof. exact (eq_refl (e = e')). Qed.
Lemma lem15176 {_2963 : Type'} (e : _2963) (e' : _2963) : (term34 _2963 e e') = (term22 _2963 e e').
Proof. exact (MK_COMB (@lem15172) (@lem15175 _2963 e e')). Qed.
Lemma lem15178 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem15179 {_2963 : Type'} (e : _2963) (e' : _2963) : (term22 _2963 e e') = (e = e').
Proof. exact (@lem15178 (e = e')). Qed.
Lemma lem15182 {_2963 : Type'} (e : _2963) (e' : _2963) : (term34 _2963 e e') = (e = e').
Proof. exact (TRANS (@lem15176 _2963 e e') (@lem15179 _2963 e e')). Qed.
Lemma lem15183 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem15184 {_2963 : Type'} (e : _2963) (e' : _2963) : (term35 _2963 e e') = (term24 _2963 e e').
Proof. exact (MK_COMB (@lem15183) (@lem15182 _2963 e e')). Qed.
Lemma lem15188 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem15189 {_2963 : Type'} (t1 : _2963) (t2 : _2963) : (@COND _2963 False t1 t2) = t2.
Proof. exact (@lem15188 _2963 t1 t2). Qed.
Lemma lem15190 {_2963 : Type'} (t' : _2963) (e' : _2963) : (@COND _2963 False t' e') = e'.
Proof. exact (@lem15189 _2963 t' e'). Qed.
Lemma lem15191 {_2963 : Type'} (e : _2963) : (@eq _2963 e) = (@eq _2963 e).
Proof. exact (eq_refl (@eq _2963 e)). Qed.
Lemma lem15192 {_2963 : Type'} (t' : _2963) (e : _2963) (e' : _2963) : (e = (@COND _2963 False t' e')) = (e = e').
Proof. exact (MK_COMB (@lem15191 _2963 e) (@lem15190 _2963 t' e')). Qed.
Lemma lem15195 {_2963 : Type'} (t' : _2963) (e : _2963) (e' : _2963) : (term36 _2963 e t' e') = (term37 _2963 e e').
Proof. exact (MK_COMB (@lem15184 _2963 e e') (@lem15192 _2963 t' e e')). Qed.
Lemma lem15199 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem15200 {_2963 : Type'} (e : _2963) (e' : _2963) : (term37 _2963 e e') = True.
Proof. exact (@lem15199 (e = e')). Qed.
Lemma lem15201 {_2963 : Type'} (e : _2963) (t' : _2963) (e' : _2963) : (term36 _2963 e t' e') = True.
Proof. exact (TRANS (@lem15195 _2963 t' e e') (@lem15200 _2963 e e')). Qed.
Lemma lem15202 {_2963 : Type'} (t : _2963) (e : _2963) (t' : _2963) (e' : _2963) : (term38 _2963 t e t' e') = (True -> True).
Proof. exact (MK_COMB (@lem15164 _2963 t t') (@lem15201 _2963 e t' e')). Qed.
Lemma lem15204 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem15205 : (True -> True) = True.
Proof. exact (@lem15204 True). Qed.
Lemma lem15206 {_2963 : Type'} (t : _2963) (e : _2963) (t' : _2963) (e' : _2963) : (term38 _2963 t e t' e') = True.
Proof. exact (TRANS (@lem15202 _2963 t e t' e') (@lem15205)). Qed.
Lemma lem15207 {_2963 : Type'} (t : _2963) (e : _2963) (t' : _2963) (e' : _2963) : (term20 _2963 t e t' e') = (True -> True).
Proof. exact (MK_COMB (@lem15157) (@lem15206 _2963 t e t' e')). Qed.
Lemma lem15209 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem15210 : (True -> True) = True.
Proof. exact (@lem15209 True). Qed.
Lemma lem15211 {_2963 : Type'} (t : _2963) (e : _2963) (t' : _2963) (e' : _2963) : (term20 _2963 t e t' e') = True.
Proof. exact (TRANS (@lem15207 _2963 t e t' e') (@lem15210)). Qed.
Lemma lem15212 {_2963 : Type'} (t : _2963) (e : _2963) (t' : _2963) (e' : _2963) : True = (term20 _2963 t e t' e').
Proof. exact (SYM (@lem15211 _2963 t e t' e')). Qed.
Lemma lem15213 {_2963 : Type'} (t : _2963) (e : _2963) (t' : _2963) (e' : _2963) : term20 _2963 t e t' e'.
Proof. exact (EQ_MP (@lem15212 _2963 t e t' e') (@lem0)). Qed.
Lemma lem15214 {_2963 : Type'} (t : _2963) (e : _2963) (t' : _2963) (e' : _2963) (g' : Prop) (h1 : g' = False) : term10 _2963 t e g' t' e'.
Proof. exact (EQ_MP (@lem15089 _2963 t e t' e' g' h1) (@lem15213 _2963 t e t' e')). Qed.
Lemma lem15215 {_2963 : Type'} (t : _2963) (e : _2963) (t' : _2963) (e' : _2963) (g' : Prop) (h1 : g' = True) : term10 _2963 t e g' t' e'.
Proof. exact (EQ_MP (@lem15076 _2963 t e t' e' g' h1) (@lem15151 _2963 t e t' e')). Qed.
Lemma lem15217 {_2963 : Type'} (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term10 _2963 t e g' t' e'.
Proof. exact (or_elim (@lem15043 g') (fun h0 : g' = True => @lem15215 _2963 t e t' e' g' h0) (fun h0 : g' = False => @lem15214 _2963 t e t' e' g' h0)). Qed.
Lemma lem15218 {_2963 : Type'} (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term9 _2963 t e g' t' e'.
Proof. exact (EQ_MP (@lem15040 _2963 t e g' t' e') (@lem15217 _2963 t e g' t' e')). Qed.
Lemma lem15219 {_2963 : Type'} (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) (g : Prop) (h1 : g = False) : term39 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14834 _2963 t e g' t' e' g h1) (@lem15218 _2963 t e g' t' e')). Qed.
