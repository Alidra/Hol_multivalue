Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1980255_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import IMP_CONJ_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import RAT_LEMMA4_spec.
Require Import REAL_NOT_LE_spec.
Require Import thm0_spec.
Require Import thm10416_spec.
Require Import thm10417_spec.
Require Import thm1821_spec.
Require Import thm1842_spec.
Require Import thm1855_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Require Import thm892_spec.
Lemma lem1980035 (a : Prop) : term0 a.
Proof. exact (@lem9851 a). Qed.
Lemma lem1980036 (a : Prop) : (term0 a) = (term1 a).
Proof. exact (eq_refl (term0 a)). Qed.
Lemma lem1980037 (a : Prop) : term1 a.
Proof. exact (EQ_MP (@lem1980036 a) (@lem1980035 a)). Qed.
Lemma lem1980038 (a : Prop) (h1 : a = True) : a = True.
Proof. exact (h1). Qed.
Lemma lem1980039 (a : Prop) (h1 : a = False) : a = False.
Proof. exact (h1). Qed.
Lemma lem1980048 (b : Prop) : (term2 b) = (term2 b).
Proof. exact (eq_refl (term2 b)). Qed.
Lemma lem1980049 (b : Prop) (a : Prop) (h1 : a = True) : (term3 b a) = (term4 b).
Proof. exact (MK_COMB (@lem1980048 b) (@lem1980038 a h1)). Qed.
Lemma lem1980050 (b : Prop) : (term4 b) = (((~ True) = (~ b)) = (True = b)).
Proof. exact (eq_refl (term4 b)). Qed.
Lemma lem1980051 (b : Prop) (a : Prop) : (term5 b a) = (term5 b a).
Proof. exact (eq_refl (term5 b a)). Qed.
Lemma lem1980052 (a : Prop) (b : Prop) : ((term3 b a) = (term4 b)) = ((term3 b a) = (((~ True) = (~ b)) = (True = b))).
Proof. exact (MK_COMB (@lem1980051 b a) (@lem1980050 b)). Qed.
Lemma lem1980053 (a : Prop) (b : Prop) : (term3 b a) = (((~ a) = (~ b)) = (a = b)).
Proof. exact (eq_refl (term3 b a)). Qed.
Lemma lem1980054 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1980055 (a : Prop) (b : Prop) : (term5 b a) = (term6 a b).
Proof. exact (MK_COMB (@lem1980054) (@lem1980053 a b)). Qed.
Lemma lem1980056 (b : Prop) : (((~ True) = (~ b)) = (True = b)) = (((~ True) = (~ b)) = (True = b)).
Proof. exact (eq_refl (((~ True) = (~ b)) = (True = b))). Qed.
Lemma lem1980057 (a : Prop) (b : Prop) : ((term3 b a) = (((~ True) = (~ b)) = (True = b))) = ((((~ a) = (~ b)) = (a = b)) = (((~ True) = (~ b)) = (True = b))).
Proof. exact (MK_COMB (@lem1980055 a b) (@lem1980056 b)). Qed.
Lemma lem1980058 (a : Prop) (b : Prop) : ((term3 b a) = (term4 b)) = ((((~ a) = (~ b)) = (a = b)) = (((~ True) = (~ b)) = (True = b))).
Proof. exact (TRANS (@lem1980052 a b) (@lem1980057 a b)). Qed.
Lemma lem1980059 (b : Prop) (a : Prop) (h1 : a = True) : (((~ a) = (~ b)) = (a = b)) = (((~ True) = (~ b)) = (True = b)).
Proof. exact (EQ_MP (@lem1980058 a b) (@lem1980049 b a h1)). Qed.
Lemma lem1980060 (b : Prop) (a : Prop) (h1 : a = True) : (((~ True) = (~ b)) = (True = b)) = (((~ a) = (~ b)) = (a = b)).
Proof. exact (SYM (@lem1980059 b a h1)). Qed.
Lemma lem1980061 (b : Prop) : (term2 b) = (term2 b).
Proof. exact (eq_refl (term2 b)). Qed.
Lemma lem1980062 (b : Prop) (a : Prop) (h1 : a = False) : (term3 b a) = (term7 b).
Proof. exact (MK_COMB (@lem1980061 b) (@lem1980039 a h1)). Qed.
Lemma lem1980063 (b : Prop) : (term7 b) = (((~ False) = (~ b)) = (False = b)).
Proof. exact (eq_refl (term7 b)). Qed.
Lemma lem1980064 (b : Prop) (a : Prop) : (term5 b a) = (term5 b a).
Proof. exact (eq_refl (term5 b a)). Qed.
Lemma lem1980065 (a : Prop) (b : Prop) : ((term3 b a) = (term7 b)) = ((term3 b a) = (((~ False) = (~ b)) = (False = b))).
Proof. exact (MK_COMB (@lem1980064 b a) (@lem1980063 b)). Qed.
Lemma lem1980066 (a : Prop) (b : Prop) : (term3 b a) = (((~ a) = (~ b)) = (a = b)).
Proof. exact (eq_refl (term3 b a)). Qed.
Lemma lem1980067 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1980068 (a : Prop) (b : Prop) : (term5 b a) = (term6 a b).
Proof. exact (MK_COMB (@lem1980067) (@lem1980066 a b)). Qed.
Lemma lem1980069 (b : Prop) : (((~ False) = (~ b)) = (False = b)) = (((~ False) = (~ b)) = (False = b)).
Proof. exact (eq_refl (((~ False) = (~ b)) = (False = b))). Qed.
Lemma lem1980070 (a : Prop) (b : Prop) : ((term3 b a) = (((~ False) = (~ b)) = (False = b))) = ((((~ a) = (~ b)) = (a = b)) = (((~ False) = (~ b)) = (False = b))).
Proof. exact (MK_COMB (@lem1980068 a b) (@lem1980069 b)). Qed.
Lemma lem1980071 (a : Prop) (b : Prop) : ((term3 b a) = (term7 b)) = ((((~ a) = (~ b)) = (a = b)) = (((~ False) = (~ b)) = (False = b))).
Proof. exact (TRANS (@lem1980065 a b) (@lem1980070 a b)). Qed.
Lemma lem1980072 (b : Prop) (a : Prop) (h1 : a = False) : (((~ a) = (~ b)) = (a = b)) = (((~ False) = (~ b)) = (False = b)).
Proof. exact (EQ_MP (@lem1980071 a b) (@lem1980062 b a h1)). Qed.
Lemma lem1980073 (b : Prop) (a : Prop) (h1 : a = False) : (((~ False) = (~ b)) = (False = b)) = (((~ a) = (~ b)) = (a = b)).
Proof. exact (SYM (@lem1980072 b a h1)). Qed.
Lemma lem1980079 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem1980080 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1980081 : term8 = (@eq Prop False).
Proof. exact (MK_COMB (@lem1980080) (@lem1980079)). Qed.
Lemma lem1980082 (b : Prop) : (~ b) = (~ b).
Proof. exact (eq_refl (~ b)). Qed.
Lemma lem1980083 (b : Prop) : ((~ True) = (~ b)) = (False = (~ b)).
Proof. exact (MK_COMB (@lem1980081) (@lem1980082 b)). Qed.
Lemma lem1980085 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem1980086 (b : Prop) : (False = (~ b)) = (term9 b).
Proof. exact (@lem1980085 (~ b)). Qed.
Lemma lem1980088 (t : Prop) : (term9 t) = t.
Proof. exact (EQ_MP (@lem10417 t) (@lem10416 t)). Qed.
Lemma lem1980089 (b : Prop) : (term9 b) = b.
Proof. exact (@lem1980088 b). Qed.
Lemma lem1980090 (b : Prop) : (False = (~ b)) = b.
Proof. exact (TRANS (@lem1980086 b) (@lem1980089 b)). Qed.
Lemma lem1980091 (b : Prop) : ((~ True) = (~ b)) = b.
Proof. exact (TRANS (@lem1980083 b) (@lem1980090 b)). Qed.
Lemma lem1980092 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1980093 (b : Prop) : (term10 b) = (@eq Prop b).
Proof. exact (MK_COMB (@lem1980092) (@lem1980091 b)). Qed.
Lemma lem1980095 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem1980096 (b : Prop) : (True = b) = b.
Proof. exact (@lem1980095 b). Qed.
Lemma lem1980097 (b : Prop) : (((~ True) = (~ b)) = (True = b)) = (b = b).
Proof. exact (MK_COMB (@lem1980093 b) (@lem1980096 b)). Qed.
Lemma lem1980099 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1980100 (x : Prop) : (x = x) = True.
Proof. exact (@lem1980099 Prop x). Qed.
Lemma lem1980101 (b : Prop) : (b = b) = True.
Proof. exact (@lem1980100 b). Qed.
Lemma lem1980102 (b : Prop) : (((~ True) = (~ b)) = (True = b)) = True.
Proof. exact (TRANS (@lem1980097 b) (@lem1980101 b)). Qed.
Lemma lem1980103 (b : Prop) : True = (((~ True) = (~ b)) = (True = b)).
Proof. exact (SYM (@lem1980102 b)). Qed.
Lemma lem1980104 (b : Prop) : ((~ True) = (~ b)) = (True = b).
Proof. exact (EQ_MP (@lem1980103 b) (@lem0)). Qed.
Lemma lem1980110 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1980111 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1980112 : term11 = (@eq Prop True).
Proof. exact (MK_COMB (@lem1980111) (@lem1980110)). Qed.
Lemma lem1980113 (b : Prop) : (~ b) = (~ b).
Proof. exact (eq_refl (~ b)). Qed.
Lemma lem1980114 (b : Prop) : ((~ False) = (~ b)) = (True = (~ b)).
Proof. exact (MK_COMB (@lem1980112) (@lem1980113 b)). Qed.
Lemma lem1980116 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem1980117 (b : Prop) : (True = (~ b)) = (~ b).
Proof. exact (@lem1980116 (~ b)). Qed.
Lemma lem1980118 (b : Prop) : ((~ False) = (~ b)) = (~ b).
Proof. exact (TRANS (@lem1980114 b) (@lem1980117 b)). Qed.
Lemma lem1980119 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1980120 (b : Prop) : (term12 b) = (term13 b).
Proof. exact (MK_COMB (@lem1980119) (@lem1980118 b)). Qed.
Lemma lem1980122 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem1980123 (b : Prop) : (False = b) = (~ b).
Proof. exact (@lem1980122 b). Qed.
Lemma lem1980124 (b : Prop) : (((~ False) = (~ b)) = (False = b)) = ((~ b) = (~ b)).
Proof. exact (MK_COMB (@lem1980120 b) (@lem1980123 b)). Qed.
Lemma lem1980126 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1980127 (x : Prop) : (x = x) = True.
Proof. exact (@lem1980126 Prop x). Qed.
Lemma lem1980128 (b : Prop) : ((~ b) = (~ b)) = True.
Proof. exact (@lem1980127 (~ b)). Qed.
Lemma lem1980129 (b : Prop) : (((~ False) = (~ b)) = (False = b)) = True.
Proof. exact (TRANS (@lem1980124 b) (@lem1980128 b)). Qed.
Lemma lem1980130 (b : Prop) : True = (((~ False) = (~ b)) = (False = b)).
Proof. exact (SYM (@lem1980129 b)). Qed.
Lemma lem1980131 (b : Prop) : ((~ False) = (~ b)) = (False = b).
Proof. exact (EQ_MP (@lem1980130 b) (@lem0)). Qed.
Lemma lem1980132 (b : Prop) (a : Prop) (h1 : a = False) : ((~ a) = (~ b)) = (a = b).
Proof. exact (EQ_MP (@lem1980073 b a h1) (@lem1980131 b)). Qed.
Lemma lem1980133 (b : Prop) (a : Prop) (h1 : a = True) : ((~ a) = (~ b)) = (a = b).
Proof. exact (EQ_MP (@lem1980060 b a h1) (@lem1980104 b)). Qed.
Lemma lem1980137 (y1 : real) (y2 : real) (h1 : term14 y1 y2) : term14 y1 y2.
Proof. exact (h1). Qed.
Lemma lem1980138 (x1 : real) (x2 : real) (y1 : real) (y2 : real) (h1 : term14 y1 y2) : (term15 x1 y1 x2 y2) = (term16 x1 y2 x2 y1).
Proof. exact (@lem1979407 x1 y2 x2 y1 (@lem1980137 y1 y2 h1)). Qed.
Lemma lem1980146 (y : real) (x : real) (h1 : (term17 x y) = (real_lt y x)) : (term17 x y) = (real_lt y x).
Proof. exact (h1). Qed.
Lemma lem1980147 (y : real) (x : real) (h1 : (term17 x y) = (real_lt y x)) : (real_lt y x) = (term17 x y).
Proof. exact (SYM (@lem1980146 y x h1)). Qed.
Lemma lem1980148 (x : real) (y : real) (h1 : (real_lt y x) = (term17 x y)) : (real_lt y x) = (term17 x y).
Proof. exact (h1). Qed.
Lemma lem1980149 (x : real) (y : real) (h1 : (real_lt y x) = (term17 x y)) : (term17 x y) = (real_lt y x).
Proof. exact (SYM (@lem1980148 x y h1)). Qed.
Lemma lem1980150 (x : real) (y : real) : ((term17 x y) = (real_lt y x)) = ((real_lt y x) = (term17 x y)).
Proof. exact (prop_ext (fun h1 : (term17 x y) = (real_lt y x) => @lem1980147 y x h1) (fun h1 : (real_lt y x) = (term17 x y) => @lem1980149 x y h1)). Qed.
Lemma lem1980151 (x : real) : (term18 x) = (term19 x).
Proof. exact (fun_ext (fun y : real => @lem1980150 x y)). Qed.
Lemma lem1980152 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1980153 (x : real) : (term20 x) = (term21 x).
Proof. exact (MK_COMB (@lem1980152) (@lem1980151 x)). Qed.
Lemma lem1980154 : term22 = term23.
Proof. exact (fun_ext (fun x : real => @lem1980153 x)). Qed.
Lemma lem1980155 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1980156 : term24 = term25.
Proof. exact (MK_COMB (@lem1980155) (@lem1980154)). Qed.
Lemma lem1980157 : term25.
Proof. exact (EQ_MP (@lem1980156) (@lem1495933)). Qed.
Lemma lem1980158 (x : real) : term26 x.
Proof. exact (@lem1980157 x). Qed.
Lemma lem1980159 (x : real) : (term26 x) = (term21 x).
Proof. exact (eq_refl (term26 x)). Qed.
Lemma lem1980160 (x : real) : term21 x.
Proof. exact (EQ_MP (@lem1980159 x) (@lem1980158 x)). Qed.
Lemma lem1980161 (x : real) (y : real) : term27 x y.
Proof. exact (@lem1980160 x y). Qed.
Lemma lem1980162 (x : real) (y : real) : (term27 x y) = ((real_lt y x) = (term17 x y)).
Proof. exact (eq_refl (term27 x y)). Qed.
Lemma lem1980165 (p : Prop) (q : Prop) (r : Prop) : (term28 p q r) = (term29 p q r).
Proof. exact (EQ_MP (@lem892 p q r) (@lem887 p q r)). Qed.
Lemma lem1980166 (x1 : real) (y2 : real) (x2 : real) (y1 : real) : (term30 x1 y2 x2 y1) = (term31 x1 y2 x2 y1).
Proof. exact (@lem1980165 (term32 y1) (term32 y2) ((term33 x1 y1 x2 y2) = (term34 x1 y2 x2 y1))). Qed.
Lemma lem1980173 (x1 : real) (y2 : real) (x2 : real) (y1 : real) : (term31 x1 y2 x2 y1) = (term30 x1 y2 x2 y1).
Proof. exact (SYM (@lem1980166 x1 y2 x2 y1)). Qed.
Lemma lem1980175 (x : real) (y : real) : (real_lt y x) = (term17 x y).
Proof. exact (EQ_MP (@lem1980162 x y) (@lem1980161 x y)). Qed.
Lemma lem1980176 (x2 : real) (y2 : real) (x1 : real) (y1 : real) : (term33 x1 y1 x2 y2) = (term35 x2 y2 x1 y1).
Proof. exact (@lem1980175 (real_div x2 y2) (real_div x1 y1)). Qed.
Lemma lem1980177 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1980178 (x2 : real) (y2 : real) (x1 : real) (y1 : real) : (term36 x1 y1 x2 y2) = (term37 x2 y2 x1 y1).
Proof. exact (MK_COMB (@lem1980177) (@lem1980176 x2 y2 x1 y1)). Qed.
Lemma lem1980180 (x : real) (y : real) : (real_lt y x) = (term17 x y).
Proof. exact (EQ_MP (@lem1980162 x y) (@lem1980161 x y)). Qed.
Lemma lem1980181 (x2 : real) (y1 : real) (x1 : real) (y2 : real) : (term34 x1 y2 x2 y1) = (term38 x2 y1 x1 y2).
Proof. exact (@lem1980180 (real_mul x2 y1) (real_mul x1 y2)). Qed.
Lemma lem1980182 (x2 : real) (y1 : real) (x1 : real) (y2 : real) : ((term33 x1 y1 x2 y2) = (term34 x1 y2 x2 y1)) = ((term35 x2 y2 x1 y1) = (term38 x2 y1 x1 y2)).
Proof. exact (MK_COMB (@lem1980178 x2 y2 x1 y1) (@lem1980181 x2 y1 x1 y2)). Qed.
Lemma lem1980183 (y1 : real) (y2 : real) : (term39 y1 y2) = (term39 y1 y2).
Proof. exact (eq_refl (term39 y1 y2)). Qed.
Lemma lem1980184 (x2 : real) (y1 : real) (x1 : real) (y2 : real) : (term31 x1 y2 x2 y1) = (term40 x2 y1 x1 y2).
Proof. exact (MK_COMB (@lem1980183 y1 y2) (@lem1980182 x2 y1 x1 y2)). Qed.
Lemma lem1980185 (x1 : real) (y2 : real) (x2 : real) (y1 : real) : (term40 x2 y1 x1 y2) = (term31 x1 y2 x2 y1).
Proof. exact (SYM (@lem1980184 x2 y1 x1 y2)). Qed.
Lemma lem1980189 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term41 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem1980190 (p : Prop) (q : Prop) (p' : Prop) : term42 p q p'.
Proof. exact (fun q' : Prop => @lem1980189 p q p' q'). Qed.
Lemma lem1980191 (p : Prop) (q : Prop) : term43 p q.
Proof. exact (fun p' : Prop => @lem1980190 p q p'). Qed.
Lemma lem1980192 (x2 : real) (y1 : real) (x1 : real) (y2 : real) : term44 x2 y1 x1 y2.
Proof. exact (@lem1980191 (term14 y1 y2) ((term35 x2 y2 x1 y1) = (term38 x2 y1 x1 y2))). Qed.
Lemma lem1980193 (x2 : real) (y1 : real) (x1 : real) (y2 : real) (p' : Prop) : term45 x2 y1 x1 y2 p'.
Proof. exact (@lem1980192 x2 y1 x1 y2 p'). Qed.
Lemma lem1980194 (x2 : real) (y1 : real) (x1 : real) (y2 : real) (p' : Prop) : (term45 x2 y1 x1 y2 p') = (term46 x2 y1 x1 y2 p').
Proof. exact (eq_refl (term45 x2 y1 x1 y2 p')). Qed.
Lemma lem1980195 (x2 : real) (y1 : real) (x1 : real) (y2 : real) (p' : Prop) : term46 x2 y1 x1 y2 p'.
Proof. exact (EQ_MP (@lem1980194 x2 y1 x1 y2 p') (@lem1980193 x2 y1 x1 y2 p')). Qed.
Lemma lem1980196 (x2 : real) (y1 : real) (x1 : real) (y2 : real) (p' : Prop) (q' : Prop) : term47 x2 y1 x1 y2 p' q'.
Proof. exact (@lem1980195 x2 y1 x1 y2 p' q'). Qed.
Lemma lem1980197 (x2 : real) (y1 : real) (x1 : real) (y2 : real) (p' : Prop) (q' : Prop) : (term47 x2 y1 x1 y2 p' q') = (term48 x2 y1 x1 y2 p' q').
Proof. exact (eq_refl (term47 x2 y1 x1 y2 p' q')). Qed.
Lemma lem1980198 (x2 : real) (y1 : real) (x1 : real) (y2 : real) (p' : Prop) (q' : Prop) : term48 x2 y1 x1 y2 p' q'.
Proof. exact (EQ_MP (@lem1980197 x2 y1 x1 y2 p' q') (@lem1980196 x2 y1 x1 y2 p' q')). Qed.
Lemma lem1980201 (y1 : real) (y2 : real) : (term14 y1 y2) = (term14 y1 y2).
Proof. exact (eq_refl (term14 y1 y2)). Qed.
Lemma lem1980202 (x2 : real) (x1 : real) (y1 : real) (y2 : real) (q' : Prop) : term49 x2 x1 y1 y2 q'.
Proof. exact (@lem1980198 x2 y1 x1 y2 (term14 y1 y2) q'). Qed.
Lemma lem1980203 (x2 : real) (x1 : real) (y1 : real) (y2 : real) (q' : Prop) : term50 x2 x1 y1 y2 q'.
Proof. exact (@lem1980202 x2 x1 y1 y2 q' (@lem1980201 y1 y2)). Qed.
Lemma lem1980204 (y1 : real) (y2 : real) (h1 : term14 y1 y2) : term14 y1 y2.
Proof. exact (h1). Qed.
Lemma lem1980205 (y1 : real) (y2 : real) (h1 : term14 y1 y2) : term32 y2.
Proof. exact (proj2 (@lem1980204 y1 y2 h1)). Qed.
Lemma lem1980206 (y2 : real) : (term32 y2) = ((term32 y2) = True).
Proof. exact (@lem7 (term32 y2)). Qed.
Lemma lem1980208 (y1 : real) (y2 : real) (h1 : term14 y1 y2) : term32 y1.
Proof. exact (proj1 (@lem1980204 y1 y2 h1)). Qed.
Lemma lem1980209 (y1 : real) : (term32 y1) = ((term32 y1) = True).
Proof. exact (@lem7 (term32 y1)). Qed.
Lemma lem1980212 (a : Prop) (b : Prop) : ((~ a) = (~ b)) = (a = b).
Proof. exact (or_elim (@lem1980037 a) (fun h0 : a = True => @lem1980133 b a h0) (fun h0 : a = False => @lem1980132 b a h0)). Qed.
Lemma lem1980213 (x2 : real) (y1 : real) (x1 : real) (y2 : real) : ((term35 x2 y2 x1 y1) = (term38 x2 y1 x1 y2)) = ((term15 x2 y2 x1 y1) = (term16 x2 y1 x1 y2)).
Proof. exact (@lem1980212 (term15 x2 y2 x1 y1) (term16 x2 y1 x1 y2)). Qed.
Lemma lem1980217 (x1 : real) (y2 : real) (x2 : real) (y1 : real) : term51 x1 y2 x2 y1.
Proof. exact (fun h0 : term14 y1 y2 => @lem1980138 x1 x2 y1 y2 h0). Qed.
Lemma lem1980218 (x2 : real) (y1 : real) (x1 : real) (y2 : real) : term51 x2 y1 x1 y2.
Proof. exact (@lem1980217 x2 y1 x1 y2). Qed.
Lemma lem1980222 (y1 : real) (y2 : real) (h1 : term14 y1 y2) : (term32 y2) = True.
Proof. exact (EQ_MP (@lem1980206 y2) (@lem1980205 y1 y2 h1)). Qed.
Lemma lem1980223 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1980224 (y1 : real) (y2 : real) (h1 : term14 y1 y2) : (term52 y2) = (and True).
Proof. exact (MK_COMB (@lem1980223) (@lem1980222 y1 y2 h1)). Qed.
Lemma lem1980226 (y1 : real) (y2 : real) (h1 : term14 y1 y2) : (term32 y1) = True.
Proof. exact (EQ_MP (@lem1980209 y1) (@lem1980208 y1 y2 h1)). Qed.
Lemma lem1980227 (y1 : real) (y2 : real) (h1 : term14 y1 y2) : (term14 y2 y1) = (True /\ True).
Proof. exact (MK_COMB (@lem1980224 y1 y2 h1) (@lem1980226 y1 y2 h1)). Qed.
Lemma lem1980229 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1980230 : (True /\ True) = True.
Proof. exact (@lem1980229 True). Qed.
Lemma lem1980231 (y1 : real) (y2 : real) (h1 : term14 y1 y2) : (term14 y2 y1) = True.
Proof. exact (TRANS (@lem1980227 y1 y2 h1) (@lem1980230)). Qed.
Lemma lem1980232 (y1 : real) (y2 : real) (h1 : term14 y1 y2) : True = (term14 y2 y1).
Proof. exact (SYM (@lem1980231 y1 y2 h1)). Qed.
Lemma lem1980233 (y1 : real) (y2 : real) (h1 : term14 y1 y2) : term14 y2 y1.
Proof. exact (EQ_MP (@lem1980232 y1 y2 h1) (@lem0)). Qed.
Lemma lem1980234 (x2 : real) (x1 : real) (y1 : real) (y2 : real) (h1 : term14 y1 y2) : (term15 x2 y2 x1 y1) = (term16 x2 y1 x1 y2).
Proof. exact (@lem1980218 x2 y1 x1 y2 (@lem1980233 y1 y2 h1)). Qed.
Lemma lem1980235 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1980236 (x2 : real) (x1 : real) (y1 : real) (y2 : real) (h1 : term14 y1 y2) : (term53 x2 y2 x1 y1) = (term54 x2 y1 x1 y2).
Proof. exact (MK_COMB (@lem1980235) (@lem1980234 x2 x1 y1 y2 h1)). Qed.
Lemma lem1980237 (x2 : real) (y1 : real) (x1 : real) (y2 : real) : (term16 x2 y1 x1 y2) = (term16 x2 y1 x1 y2).
Proof. exact (eq_refl (term16 x2 y1 x1 y2)). Qed.
Lemma lem1980238 (x2 : real) (x1 : real) (y1 : real) (y2 : real) (h1 : term14 y1 y2) : ((term15 x2 y2 x1 y1) = (term16 x2 y1 x1 y2)) = ((term16 x2 y1 x1 y2) = (term16 x2 y1 x1 y2)).
Proof. exact (MK_COMB (@lem1980236 x2 x1 y1 y2 h1) (@lem1980237 x2 y1 x1 y2)). Qed.
Lemma lem1980240 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1980241 (x : Prop) : (x = x) = True.
Proof. exact (@lem1980240 Prop x). Qed.
Lemma lem1980242 (x2 : real) (y1 : real) (x1 : real) (y2 : real) : ((term16 x2 y1 x1 y2) = (term16 x2 y1 x1 y2)) = True.
Proof. exact (@lem1980241 (term16 x2 y1 x1 y2)). Qed.
Lemma lem1980243 (x2 : real) (x1 : real) (y1 : real) (y2 : real) (h1 : term14 y1 y2) : ((term15 x2 y2 x1 y1) = (term16 x2 y1 x1 y2)) = True.
Proof. exact (TRANS (@lem1980238 x2 x1 y1 y2 h1) (@lem1980242 x2 y1 x1 y2)). Qed.
Lemma lem1980244 (x2 : real) (x1 : real) (y1 : real) (y2 : real) (h1 : term14 y1 y2) : ((term35 x2 y2 x1 y1) = (term38 x2 y1 x1 y2)) = True.
Proof. exact (TRANS (@lem1980213 x2 y1 x1 y2) (@lem1980243 x2 x1 y1 y2 h1)). Qed.
Lemma lem1980245 (x2 : real) (y1 : real) (x1 : real) (y2 : real) : term55 x2 y1 x1 y2.
Proof. exact (fun h0 : term14 y1 y2 => @lem1980244 x2 x1 y1 y2 h0). Qed.
Lemma lem1980246 (x2 : real) (x1 : real) (y1 : real) (y2 : real) : term56 x2 x1 y1 y2.
Proof. exact (@lem1980203 x2 x1 y1 y2 True). Qed.
Lemma lem1980247 (x2 : real) (x1 : real) (y1 : real) (y2 : real) : (term40 x2 y1 x1 y2) = (term57 y1 y2).
Proof. exact (@lem1980246 x2 x1 y1 y2 (@lem1980245 x2 y1 x1 y2)). Qed.
Lemma lem1980249 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem1980250 (y1 : real) (y2 : real) : (term57 y1 y2) = True.
Proof. exact (@lem1980249 (term14 y1 y2)). Qed.
Lemma lem1980251 (x2 : real) (y1 : real) (x1 : real) (y2 : real) : (term40 x2 y1 x1 y2) = True.
Proof. exact (TRANS (@lem1980247 x2 x1 y1 y2) (@lem1980250 y1 y2)). Qed.
Lemma lem1980252 (x2 : real) (y1 : real) (x1 : real) (y2 : real) : True = (term40 x2 y1 x1 y2).
Proof. exact (SYM (@lem1980251 x2 y1 x1 y2)). Qed.
Lemma lem1980253 (x2 : real) (y1 : real) (x1 : real) (y2 : real) : term40 x2 y1 x1 y2.
Proof. exact (EQ_MP (@lem1980252 x2 y1 x1 y2) (@lem0)). Qed.
Lemma lem1980254 (x1 : real) (y2 : real) (x2 : real) (y1 : real) : term31 x1 y2 x2 y1.
Proof. exact (EQ_MP (@lem1980185 x1 y2 x2 y1) (@lem1980253 x2 y1 x1 y2)). Qed.
Lemma lem1980255 (x1 : real) (y2 : real) (x2 : real) (y1 : real) : term30 x1 y2 x2 y1.
Proof. exact (EQ_MP (@lem1980173 x1 y2 x2 y1) (@lem1980254 x1 y2 x2 y1)). Qed.
