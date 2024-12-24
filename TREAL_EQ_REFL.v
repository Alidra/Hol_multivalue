Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import TREAL_EQ_REFL_term_abbrevs.
Require Import FORALL_PAIR_THM_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import treal_eq_spec.
Lemma lem1326117 (x1 : hreal) : term0 x1.
Proof. exact (@lem1326116 x1). Qed.
Lemma lem1326118 (x1 : hreal) : (term0 x1) = (term1 x1).
Proof. exact (eq_refl (term0 x1)). Qed.
Lemma lem1326119 (x1 : hreal) : term1 x1.
Proof. exact (EQ_MP (@lem1326118 x1) (@lem1326117 x1)). Qed.
Lemma lem1326120 (x1 : hreal) (y2 : hreal) : term2 x1 y2.
Proof. exact (@lem1326119 x1 y2). Qed.
Lemma lem1326121 (x1 : hreal) (y2 : hreal) : (term2 x1 y2) = (term3 x1 y2).
Proof. exact (eq_refl (term2 x1 y2)). Qed.
Lemma lem1326122 (x1 : hreal) (y2 : hreal) : term3 x1 y2.
Proof. exact (EQ_MP (@lem1326121 x1 y2) (@lem1326120 x1 y2)). Qed.
Lemma lem1326123 (x1 : hreal) (y2 : hreal) (x2 : hreal) : term4 x1 y2 x2.
Proof. exact (@lem1326122 x1 y2 x2). Qed.
Lemma lem1326124 (x1 : hreal) (y2 : hreal) (x2 : hreal) : (term4 x1 y2 x2) = (term5 x1 y2 x2).
Proof. exact (eq_refl (term4 x1 y2 x2)). Qed.
Lemma lem1326125 (x1 : hreal) (y2 : hreal) (x2 : hreal) : term5 x1 y2 x2.
Proof. exact (EQ_MP (@lem1326124 x1 y2 x2) (@lem1326123 x1 y2 x2)). Qed.
Lemma lem1326126 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : term6 x1 y2 x2 y1.
Proof. exact (@lem1326125 x1 y2 x2 y1). Qed.
Lemma lem1326127 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : (term6 x1 y2 x2 y1) = ((term7 x1 y1 x2 y2) = ((hreal_add x1 y2) = (hreal_add x2 y1))).
Proof. exact (eq_refl (term6 x1 y2 x2 y1)). Qed.
Lemma lem1326129 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : term8 _5106 _5107 P.
Proof. exact (@lem49909 _5106 _5107 P). Qed.
Lemma lem1326130 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term8 _5106 _5107 P) = ((term9 _5106 _5107 P) = (term10 _5106 _5107 P)).
Proof. exact (eq_refl (term8 _5106 _5107 P)). Qed.
Lemma lem1326137 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term9 _5106 _5107 P) = (term10 _5106 _5107 P).
Proof. exact (EQ_MP (@lem1326130 _5106 _5107 P) (@lem1326129 _5106 _5107 P)). Qed.
Lemma lem1326138 (P : type1233) : (term11 P) = (term12 P).
Proof. exact (@lem1326137 hreal hreal P). Qed.
Lemma lem1326139 : term13 = term14.
Proof. exact (@lem1326138 term15). Qed.
Lemma lem1326140 (x : prod hreal hreal) : (term16 x) = (treal_eq x x).
Proof. exact (eq_refl (term16 x)). Qed.
Lemma lem1326141 : term17 = term15.
Proof. exact (fun_ext (fun x : prod hreal hreal => @lem1326140 x)). Qed.
Lemma lem1326142 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1326143 : term13 = term18.
Proof. exact (MK_COMB (@lem1326142) (@lem1326141)). Qed.
Lemma lem1326144 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1326145 : term19 = term20.
Proof. exact (MK_COMB (@lem1326144) (@lem1326143)). Qed.
Lemma lem1326146 (p1 : hreal) (p2 : hreal) : (term21 p1 p2) = (term22 p1 p2).
Proof. exact (eq_refl (term21 p1 p2)). Qed.
Lemma lem1326147 (p1 : hreal) : (term23 p1) = (term24 p1).
Proof. exact (fun_ext (fun p2 : hreal => @lem1326146 p1 p2)). Qed.
Lemma lem1326148 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1326149 (p1 : hreal) : (term25 p1) = (term26 p1).
Proof. exact (MK_COMB (@lem1326148) (@lem1326147 p1)). Qed.
Lemma lem1326150 : term27 = term28.
Proof. exact (fun_ext (fun p1 : hreal => @lem1326149 p1)). Qed.
Lemma lem1326151 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1326152 : term14 = term29.
Proof. exact (MK_COMB (@lem1326151) (@lem1326150)). Qed.
Lemma lem1326153 : (term13 = term14) = (term18 = term29).
Proof. exact (MK_COMB (@lem1326145) (@lem1326152)). Qed.
Lemma lem1326154 : term18 = term29.
Proof. exact (EQ_MP (@lem1326153) (@lem1326139)). Qed.
Lemma lem1326168 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : (term7 x1 y1 x2 y2) = ((hreal_add x1 y2) = (hreal_add x2 y1)).
Proof. exact (EQ_MP (@lem1326127 x1 y2 x2 y1) (@lem1326126 x1 y2 x2 y1)). Qed.
Lemma lem1326169 (p1 : hreal) (p2 : hreal) : (term22 p1 p2) = ((hreal_add p1 p2) = (hreal_add p1 p2)).
Proof. exact (@lem1326168 p1 p2 p1 p2). Qed.
Lemma lem1326171 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1326172 (x : hreal) : (x = x) = True.
Proof. exact (@lem1326171 hreal x). Qed.
Lemma lem1326173 (p1 : hreal) (p2 : hreal) : ((hreal_add p1 p2) = (hreal_add p1 p2)) = True.
Proof. exact (@lem1326172 (hreal_add p1 p2)). Qed.
Lemma lem1326174 (p1 : hreal) (p2 : hreal) : (term22 p1 p2) = True.
Proof. exact (TRANS (@lem1326169 p1 p2) (@lem1326173 p1 p2)). Qed.
Lemma lem1326175 (p1 : hreal) : (term24 p1) = term30.
Proof. exact (fun_ext (fun p2 : hreal => @lem1326174 p1 p2)). Qed.
Lemma lem1326176 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1326177 (p1 : hreal) : (term26 p1) = term31.
Proof. exact (MK_COMB (@lem1326176) (@lem1326175 p1)). Qed.
Lemma lem1326179 {A : Type'} (t : Prop) : (term32 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1326180 (t : Prop) : (term33 t) = t.
Proof. exact (@lem1326179 hreal t). Qed.
Lemma lem1326181 : term31 = True.
Proof. exact (@lem1326180 True). Qed.
Lemma lem1326182 (p1 : hreal) : (term26 p1) = True.
Proof. exact (TRANS (@lem1326177 p1) (@lem1326181)). Qed.
Lemma lem1326183 : term28 = term30.
Proof. exact (fun_ext (fun p1 : hreal => @lem1326182 p1)). Qed.
Lemma lem1326184 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1326185 : term29 = term31.
Proof. exact (MK_COMB (@lem1326184) (@lem1326183)). Qed.
Lemma lem1326187 {A : Type'} (t : Prop) : (term32 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1326188 (t : Prop) : (term33 t) = t.
Proof. exact (@lem1326187 hreal t). Qed.
Lemma lem1326189 : term31 = True.
Proof. exact (@lem1326188 True). Qed.
Lemma lem1326190 : term29 = True.
Proof. exact (TRANS (@lem1326185) (@lem1326189)). Qed.
Lemma lem1326191 : term18 = True.
Proof. exact (TRANS (@lem1326154) (@lem1326190)). Qed.
Lemma lem1326192 : True = term18.
Proof. exact (SYM (@lem1326191)). Qed.
Lemma lem1326193 : term18.
Proof. exact (EQ_MP (@lem1326192) (@lem0)). Qed.
