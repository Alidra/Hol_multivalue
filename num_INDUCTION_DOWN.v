Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import num_INDUCTION_DOWN_term_abbrevs.
Require Import ADD1_spec.
Require Import BOOL_CASES_AX_spec.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import LT_spec.
Require Import LTE_CASES_spec.
Require Import LT_IMP_LE_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_EXISTS_THM_spec.
Require Import NOT_LE_spec.
Require Import num_MAX_spec.
Require Import thm0_spec.
Require Import thm10416_spec.
Require Import thm10417_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16464_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm1820_spec.
Require Import thm1821_spec.
Require Import thm1822_spec.
Require Import thm1823_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1844_spec.
Require Import thm1845_spec.
Require Import thm1855_spec.
Require Import thm1856_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19490_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm69_spec.
Lemma lem120110 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem120111 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem120112 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem120111 t1) (@lem120110 t1)). Qed.
Lemma lem120113 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem120112 t1 t2). Qed.
Lemma lem120114 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem120115 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem120114 t1 t2) (@lem120113 t1 t2)). Qed.
Lemma lem120116 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem120115 t1 t2 t3). Qed.
Lemma lem120117 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem120118 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem120117 t1 t2 t3) (@lem120116 t1 t2 t3)). Qed.
Lemma lem120119 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem120118 t1 t2 t3)). Qed.
Lemma lem120128 (p : Prop) : term7 p.
Proof. exact (@lem9851 p). Qed.
Lemma lem120129 (p : Prop) : (term7 p) = (term8 p).
Proof. exact (eq_refl (term7 p)). Qed.
Lemma lem120130 (p : Prop) : term8 p.
Proof. exact (EQ_MP (@lem120129 p) (@lem120128 p)). Qed.
Lemma lem120131 (p : Prop) (h1 : p = True) : p = True.
Proof. exact (h1). Qed.
Lemma lem120132 (p : Prop) (h1 : p = False) : p = False.
Proof. exact (h1). Qed.
Lemma lem120141 (q : Prop) : (term9 q) = (term9 q).
Proof. exact (eq_refl (term9 q)). Qed.
Lemma lem120142 (q : Prop) (p : Prop) (h1 : p = True) : (term10 q p) = (term11 q).
Proof. exact (MK_COMB (@lem120141 q) (@lem120131 p h1)). Qed.
Lemma lem120143 (q : Prop) : (term11 q) = ((term12 q) = (q -> True)).
Proof. exact (eq_refl (term11 q)). Qed.
Lemma lem120144 (q : Prop) (p : Prop) : (term13 q p) = (term13 q p).
Proof. exact (eq_refl (term13 q p)). Qed.
Lemma lem120145 (p : Prop) (q : Prop) : ((term10 q p) = (term11 q)) = ((term10 q p) = ((term12 q) = (q -> True))).
Proof. exact (MK_COMB (@lem120144 q p) (@lem120143 q)). Qed.
Lemma lem120146 (q : Prop) (p : Prop) : (term10 q p) = ((term14 p q) = (q -> p)).
Proof. exact (eq_refl (term10 q p)). Qed.
Lemma lem120147 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem120148 (q : Prop) (p : Prop) : (term13 q p) = (term15 q p).
Proof. exact (MK_COMB (@lem120147) (@lem120146 q p)). Qed.
Lemma lem120149 (q : Prop) : ((term12 q) = (q -> True)) = ((term12 q) = (q -> True)).
Proof. exact (eq_refl ((term12 q) = (q -> True))). Qed.
Lemma lem120150 (p : Prop) (q : Prop) : ((term10 q p) = ((term12 q) = (q -> True))) = (((term14 p q) = (q -> p)) = ((term12 q) = (q -> True))).
Proof. exact (MK_COMB (@lem120148 q p) (@lem120149 q)). Qed.
Lemma lem120151 (p : Prop) (q : Prop) : ((term10 q p) = (term11 q)) = (((term14 p q) = (q -> p)) = ((term12 q) = (q -> True))).
Proof. exact (TRANS (@lem120145 p q) (@lem120150 p q)). Qed.
Lemma lem120152 (q : Prop) (p : Prop) (h1 : p = True) : ((term14 p q) = (q -> p)) = ((term12 q) = (q -> True)).
Proof. exact (EQ_MP (@lem120151 p q) (@lem120142 q p h1)). Qed.
Lemma lem120153 (q : Prop) (p : Prop) (h1 : p = True) : ((term12 q) = (q -> True)) = ((term14 p q) = (q -> p)).
Proof. exact (SYM (@lem120152 q p h1)). Qed.
Lemma lem120154 (q : Prop) : (term9 q) = (term9 q).
Proof. exact (eq_refl (term9 q)). Qed.
Lemma lem120155 (q : Prop) (p : Prop) (h1 : p = False) : (term10 q p) = (term16 q).
Proof. exact (MK_COMB (@lem120154 q) (@lem120132 p h1)). Qed.
Lemma lem120156 (q : Prop) : (term16 q) = ((term17 q) = (q -> False)).
Proof. exact (eq_refl (term16 q)). Qed.
Lemma lem120157 (q : Prop) (p : Prop) : (term13 q p) = (term13 q p).
Proof. exact (eq_refl (term13 q p)). Qed.
Lemma lem120158 (p : Prop) (q : Prop) : ((term10 q p) = (term16 q)) = ((term10 q p) = ((term17 q) = (q -> False))).
Proof. exact (MK_COMB (@lem120157 q p) (@lem120156 q)). Qed.
Lemma lem120159 (q : Prop) (p : Prop) : (term10 q p) = ((term14 p q) = (q -> p)).
Proof. exact (eq_refl (term10 q p)). Qed.
Lemma lem120160 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem120161 (q : Prop) (p : Prop) : (term13 q p) = (term15 q p).
Proof. exact (MK_COMB (@lem120160) (@lem120159 q p)). Qed.
Lemma lem120162 (q : Prop) : ((term17 q) = (q -> False)) = ((term17 q) = (q -> False)).
Proof. exact (eq_refl ((term17 q) = (q -> False))). Qed.
Lemma lem120163 (p : Prop) (q : Prop) : ((term10 q p) = ((term17 q) = (q -> False))) = (((term14 p q) = (q -> p)) = ((term17 q) = (q -> False))).
Proof. exact (MK_COMB (@lem120161 q p) (@lem120162 q)). Qed.
Lemma lem120164 (p : Prop) (q : Prop) : ((term10 q p) = (term16 q)) = (((term14 p q) = (q -> p)) = ((term17 q) = (q -> False))).
Proof. exact (TRANS (@lem120158 p q) (@lem120163 p q)). Qed.
Lemma lem120165 (q : Prop) (p : Prop) (h1 : p = False) : ((term14 p q) = (q -> p)) = ((term17 q) = (q -> False)).
Proof. exact (EQ_MP (@lem120164 p q) (@lem120155 q p h1)). Qed.
Lemma lem120166 (q : Prop) (p : Prop) (h1 : p = False) : ((term17 q) = (q -> False)) = ((term14 p q) = (q -> p)).
Proof. exact (SYM (@lem120165 q p h1)). Qed.
Lemma lem120172 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem120173 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem120174 : term18 = (and False).
Proof. exact (MK_COMB (@lem120173) (@lem120172)). Qed.
Lemma lem120175 (q : Prop) : q = q.
Proof. exact (eq_refl q). Qed.
Lemma lem120176 (q : Prop) : (term19 q) = (False /\ q).
Proof. exact (MK_COMB (@lem120174) (@lem120175 q)). Qed.
Lemma lem120178 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem120179 (q : Prop) : (False /\ q) = False.
Proof. exact (@lem120178 q). Qed.
Lemma lem120180 (q : Prop) : (term19 q) = False.
Proof. exact (TRANS (@lem120176 q) (@lem120179 q)). Qed.
Lemma lem120181 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem120182 (q : Prop) : (term12 q) = (~ False).
Proof. exact (MK_COMB (@lem120181) (@lem120180 q)). Qed.
Lemma lem120184 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem120185 (q : Prop) : (term12 q) = True.
Proof. exact (TRANS (@lem120182 q) (@lem120184)). Qed.
Lemma lem120186 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem120187 (q : Prop) : (term20 q) = (@eq Prop True).
Proof. exact (MK_COMB (@lem120186) (@lem120185 q)). Qed.
Lemma lem120189 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem120190 (q : Prop) : (q -> True) = True.
Proof. exact (@lem120189 q). Qed.
Lemma lem120191 (q : Prop) : ((term12 q) = (q -> True)) = (True = True).
Proof. exact (MK_COMB (@lem120187 q) (@lem120190 q)). Qed.
Lemma lem120193 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem120194 : (True = True) = True.
Proof. exact (@lem120193 True). Qed.
Lemma lem120195 (q : Prop) : ((term12 q) = (q -> True)) = True.
Proof. exact (TRANS (@lem120191 q) (@lem120194)). Qed.
Lemma lem120196 (q : Prop) : True = ((term12 q) = (q -> True)).
Proof. exact (SYM (@lem120195 q)). Qed.
Lemma lem120197 (q : Prop) : (term12 q) = (q -> True).
Proof. exact (EQ_MP (@lem120196 q) (@lem0)). Qed.
Lemma lem120203 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem120204 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem120205 : term21 = (and True).
Proof. exact (MK_COMB (@lem120204) (@lem120203)). Qed.
Lemma lem120206 (q : Prop) : q = q.
Proof. exact (eq_refl q). Qed.
Lemma lem120207 (q : Prop) : (term22 q) = (True /\ q).
Proof. exact (MK_COMB (@lem120205) (@lem120206 q)). Qed.
Lemma lem120209 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem120210 (q : Prop) : (True /\ q) = q.
Proof. exact (@lem120209 q). Qed.
Lemma lem120211 (q : Prop) : (term22 q) = q.
Proof. exact (TRANS (@lem120207 q) (@lem120210 q)). Qed.
Lemma lem120212 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem120213 (q : Prop) : (term17 q) = (~ q).
Proof. exact (MK_COMB (@lem120212) (@lem120211 q)). Qed.
Lemma lem120214 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem120215 (q : Prop) : (term23 q) = (term24 q).
Proof. exact (MK_COMB (@lem120214) (@lem120213 q)). Qed.
Lemma lem120217 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem120218 (q : Prop) : (q -> False) = (~ q).
Proof. exact (@lem120217 q). Qed.
Lemma lem120219 (q : Prop) : ((term17 q) = (q -> False)) = ((~ q) = (~ q)).
Proof. exact (MK_COMB (@lem120215 q) (@lem120218 q)). Qed.
Lemma lem120221 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem120222 (x : Prop) : (x = x) = True.
Proof. exact (@lem120221 Prop x). Qed.
Lemma lem120223 (q : Prop) : ((~ q) = (~ q)) = True.
Proof. exact (@lem120222 (~ q)). Qed.
Lemma lem120224 (q : Prop) : ((term17 q) = (q -> False)) = True.
Proof. exact (TRANS (@lem120219 q) (@lem120223 q)). Qed.
Lemma lem120225 (q : Prop) : True = ((term17 q) = (q -> False)).
Proof. exact (SYM (@lem120224 q)). Qed.
Lemma lem120226 (q : Prop) : (term17 q) = (q -> False).
Proof. exact (EQ_MP (@lem120225 q) (@lem0)). Qed.
Lemma lem120227 (q : Prop) (p : Prop) (h1 : p = False) : (term14 p q) = (q -> p).
Proof. exact (EQ_MP (@lem120166 q p h1) (@lem120226 q)). Qed.
Lemma lem120228 (q : Prop) (p : Prop) (h1 : p = True) : (term14 p q) = (q -> p).
Proof. exact (EQ_MP (@lem120153 q p h1) (@lem120197 q)). Qed.
Lemma lem120232 (m : nat) : term25 m.
Proof. exact (@lem97961 m). Qed.
Lemma lem120233 (m : nat) : (term25 m) = (term26 m).
Proof. exact (eq_refl (term25 m)). Qed.
Lemma lem120234 (m : nat) : term26 m.
Proof. exact (EQ_MP (@lem120233 m) (@lem120232 m)). Qed.
Lemma lem120235 (m : nat) (n : nat) : term27 m n.
Proof. exact (@lem120234 m n). Qed.
Lemma lem120236 (n : nat) (m : nat) : (term27 m n) = ((term28 m n) = (Peano.lt n m)).
Proof. exact (eq_refl (term27 m n)). Qed.
Lemma lem120238 {A : Type'} (P : A -> Prop) : term29 A P.
Proof. exact (@lem10660 A P). Qed.
Lemma lem120239 {A : Type'} (P : A -> Prop) : (term29 A P) = ((term30 A P) = (term31 A P)).
Proof. exact (eq_refl (term29 A P)). Qed.
Lemma lem120249 (p : Prop) : term7 p.
Proof. exact (@lem9851 p). Qed.
Lemma lem120250 (p : Prop) : (term7 p) = (term8 p).
Proof. exact (eq_refl (term7 p)). Qed.
Lemma lem120251 (p : Prop) : term8 p.
Proof. exact (EQ_MP (@lem120250 p) (@lem120249 p)). Qed.
Lemma lem120252 (p : Prop) (h1 : p = True) : p = True.
Proof. exact (h1). Qed.
Lemma lem120253 (p : Prop) (h1 : p = False) : p = False.
Proof. exact (h1). Qed.
Lemma lem120262 (q : Prop) : (term32 q) = (term32 q).
Proof. exact (eq_refl (term32 q)). Qed.
Lemma lem120263 (q : Prop) (p : Prop) (h1 : p = True) : (term33 q p) = (term34 q).
Proof. exact (MK_COMB (@lem120262 q) (@lem120252 p h1)). Qed.
Lemma lem120264 (q : Prop) : (term34 q) = ((term35 q) = (term36 q)).
Proof. exact (eq_refl (term34 q)). Qed.
Lemma lem120265 (q : Prop) (p : Prop) : (term37 q p) = (term37 q p).
Proof. exact (eq_refl (term37 q p)). Qed.
Lemma lem120266 (p : Prop) (q : Prop) : ((term33 q p) = (term34 q)) = ((term33 q p) = ((term35 q) = (term36 q))).
Proof. exact (MK_COMB (@lem120265 q p) (@lem120264 q)). Qed.
Lemma lem120267 (q : Prop) (p : Prop) : (term33 q p) = ((term38 p q) = (term38 q p)).
Proof. exact (eq_refl (term33 q p)). Qed.
Lemma lem120268 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem120269 (q : Prop) (p : Prop) : (term37 q p) = (term39 q p).
Proof. exact (MK_COMB (@lem120268) (@lem120267 q p)). Qed.
Lemma lem120270 (q : Prop) : ((term35 q) = (term36 q)) = ((term35 q) = (term36 q)).
Proof. exact (eq_refl ((term35 q) = (term36 q))). Qed.
Lemma lem120271 (p : Prop) (q : Prop) : ((term33 q p) = ((term35 q) = (term36 q))) = (((term38 p q) = (term38 q p)) = ((term35 q) = (term36 q))).
Proof. exact (MK_COMB (@lem120269 q p) (@lem120270 q)). Qed.
Lemma lem120272 (p : Prop) (q : Prop) : ((term33 q p) = (term34 q)) = (((term38 p q) = (term38 q p)) = ((term35 q) = (term36 q))).
Proof. exact (TRANS (@lem120266 p q) (@lem120271 p q)). Qed.
Lemma lem120273 (q : Prop) (p : Prop) (h1 : p = True) : ((term38 p q) = (term38 q p)) = ((term35 q) = (term36 q)).
Proof. exact (EQ_MP (@lem120272 p q) (@lem120263 q p h1)). Qed.
Lemma lem120274 (q : Prop) (p : Prop) (h1 : p = True) : ((term35 q) = (term36 q)) = ((term38 p q) = (term38 q p)).
Proof. exact (SYM (@lem120273 q p h1)). Qed.
Lemma lem120275 (q : Prop) : (term32 q) = (term32 q).
Proof. exact (eq_refl (term32 q)). Qed.
Lemma lem120276 (q : Prop) (p : Prop) (h1 : p = False) : (term33 q p) = (term40 q).
Proof. exact (MK_COMB (@lem120275 q) (@lem120253 p h1)). Qed.
Lemma lem120277 (q : Prop) : (term40 q) = ((term41 q) = (term42 q)).
Proof. exact (eq_refl (term40 q)). Qed.
Lemma lem120278 (q : Prop) (p : Prop) : (term37 q p) = (term37 q p).
Proof. exact (eq_refl (term37 q p)). Qed.
Lemma lem120279 (p : Prop) (q : Prop) : ((term33 q p) = (term40 q)) = ((term33 q p) = ((term41 q) = (term42 q))).
Proof. exact (MK_COMB (@lem120278 q p) (@lem120277 q)). Qed.
Lemma lem120280 (q : Prop) (p : Prop) : (term33 q p) = ((term38 p q) = (term38 q p)).
Proof. exact (eq_refl (term33 q p)). Qed.
Lemma lem120281 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem120282 (q : Prop) (p : Prop) : (term37 q p) = (term39 q p).
Proof. exact (MK_COMB (@lem120281) (@lem120280 q p)). Qed.
Lemma lem120283 (q : Prop) : ((term41 q) = (term42 q)) = ((term41 q) = (term42 q)).
Proof. exact (eq_refl ((term41 q) = (term42 q))). Qed.
Lemma lem120284 (p : Prop) (q : Prop) : ((term33 q p) = ((term41 q) = (term42 q))) = (((term38 p q) = (term38 q p)) = ((term41 q) = (term42 q))).
Proof. exact (MK_COMB (@lem120282 q p) (@lem120283 q)). Qed.
Lemma lem120285 (p : Prop) (q : Prop) : ((term33 q p) = (term40 q)) = (((term38 p q) = (term38 q p)) = ((term41 q) = (term42 q))).
Proof. exact (TRANS (@lem120279 p q) (@lem120284 p q)). Qed.
Lemma lem120286 (q : Prop) (p : Prop) (h1 : p = False) : ((term38 p q) = (term38 q p)) = ((term41 q) = (term42 q)).
Proof. exact (EQ_MP (@lem120285 p q) (@lem120276 q p h1)). Qed.
Lemma lem120287 (q : Prop) (p : Prop) (h1 : p = False) : ((term41 q) = (term42 q)) = ((term38 p q) = (term38 q p)).
Proof. exact (SYM (@lem120286 q p h1)). Qed.
Lemma lem120293 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem120294 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem120295 : term43 = (imp False).
Proof. exact (MK_COMB (@lem120294) (@lem120293)). Qed.
Lemma lem120296 (q : Prop) : q = q.
Proof. exact (eq_refl q). Qed.
Lemma lem120297 (q : Prop) : (term35 q) = (False -> q).
Proof. exact (MK_COMB (@lem120295) (@lem120296 q)). Qed.
Lemma lem120299 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem120300 (q : Prop) : (False -> q) = True.
Proof. exact (@lem120299 q). Qed.
Lemma lem120301 (q : Prop) : (term35 q) = True.
Proof. exact (TRANS (@lem120297 q) (@lem120300 q)). Qed.
Lemma lem120302 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem120303 (q : Prop) : (term44 q) = (@eq Prop True).
Proof. exact (MK_COMB (@lem120302) (@lem120301 q)). Qed.
Lemma lem120305 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem120306 (q : Prop) : (term36 q) = True.
Proof. exact (@lem120305 (~ q)). Qed.
Lemma lem120307 (q : Prop) : ((term35 q) = (term36 q)) = (True = True).
Proof. exact (MK_COMB (@lem120303 q) (@lem120306 q)). Qed.
Lemma lem120309 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem120310 : (True = True) = True.
Proof. exact (@lem120309 True). Qed.
Lemma lem120311 (q : Prop) : ((term35 q) = (term36 q)) = True.
Proof. exact (TRANS (@lem120307 q) (@lem120310)). Qed.
Lemma lem120312 (q : Prop) : True = ((term35 q) = (term36 q)).
Proof. exact (SYM (@lem120311 q)). Qed.
Lemma lem120313 (q : Prop) : (term35 q) = (term36 q).
Proof. exact (EQ_MP (@lem120312 q) (@lem0)). Qed.
Lemma lem120319 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem120320 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem120321 : term45 = (imp True).
Proof. exact (MK_COMB (@lem120320) (@lem120319)). Qed.
Lemma lem120322 (q : Prop) : q = q.
Proof. exact (eq_refl q). Qed.
Lemma lem120323 (q : Prop) : (term41 q) = (True -> q).
Proof. exact (MK_COMB (@lem120321) (@lem120322 q)). Qed.
Lemma lem120325 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem120326 (q : Prop) : (True -> q) = q.
Proof. exact (@lem120325 q). Qed.
Lemma lem120327 (q : Prop) : (term41 q) = q.
Proof. exact (TRANS (@lem120323 q) (@lem120326 q)). Qed.
Lemma lem120328 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem120329 (q : Prop) : (term46 q) = (@eq Prop q).
Proof. exact (MK_COMB (@lem120328) (@lem120327 q)). Qed.
Lemma lem120331 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem120332 (q : Prop) : (term42 q) = (term47 q).
Proof. exact (@lem120331 (~ q)). Qed.
Lemma lem120334 (t : Prop) : (term47 t) = t.
Proof. exact (EQ_MP (@lem10417 t) (@lem10416 t)). Qed.
Lemma lem120335 (q : Prop) : (term47 q) = q.
Proof. exact (@lem120334 q). Qed.
Lemma lem120336 (q : Prop) : (term42 q) = q.
Proof. exact (TRANS (@lem120332 q) (@lem120335 q)). Qed.
Lemma lem120337 (q : Prop) : ((term41 q) = (term42 q)) = (q = q).
Proof. exact (MK_COMB (@lem120329 q) (@lem120336 q)). Qed.
Lemma lem120339 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem120340 (x : Prop) : (x = x) = True.
Proof. exact (@lem120339 Prop x). Qed.
Lemma lem120341 (q : Prop) : (q = q) = True.
Proof. exact (@lem120340 q). Qed.
Lemma lem120342 (q : Prop) : ((term41 q) = (term42 q)) = True.
Proof. exact (TRANS (@lem120337 q) (@lem120341 q)). Qed.
Lemma lem120343 (q : Prop) : True = ((term41 q) = (term42 q)).
Proof. exact (SYM (@lem120342 q)). Qed.
Lemma lem120344 (q : Prop) : (term41 q) = (term42 q).
Proof. exact (EQ_MP (@lem120343 q) (@lem0)). Qed.
Lemma lem120345 (q : Prop) (p : Prop) (h1 : p = False) : (term38 p q) = (term38 q p).
Proof. exact (EQ_MP (@lem120287 q p h1) (@lem120344 q)). Qed.
Lemma lem120346 (q : Prop) (p : Prop) (h1 : p = True) : (term38 p q) = (term38 q p).
Proof. exact (EQ_MP (@lem120274 q p h1) (@lem120313 q)). Qed.
Lemma lem120364 (q : Prop) : term7 q.
Proof. exact (@lem9851 q). Qed.
Lemma lem120365 (q : Prop) : (term7 q) = (term8 q).
Proof. exact (eq_refl (term7 q)). Qed.
Lemma lem120366 (q : Prop) : term8 q.
Proof. exact (EQ_MP (@lem120365 q) (@lem120364 q)). Qed.
Lemma lem120367 (q : Prop) (h1 : q = True) : q = True.
Proof. exact (h1). Qed.
Lemma lem120368 (q : Prop) (h1 : q = False) : q = False.
Proof. exact (h1). Qed.
Lemma lem120383 (r : Prop) (p : Prop) : (term48 r p) = (term48 r p).
Proof. exact (eq_refl (term48 r p)). Qed.
Lemma lem120384 (r : Prop) (p : Prop) (q : Prop) (h1 : q = True) : (term49 r p q) = (term50 r p).
Proof. exact (MK_COMB (@lem120383 r p) (@lem120367 q h1)). Qed.
Lemma lem120385 (r : Prop) (p : Prop) : (term50 r p) = (term51 r p).
Proof. exact (eq_refl (term50 r p)). Qed.
Lemma lem120386 (r : Prop) (p : Prop) (q : Prop) : (term52 r p q) = (term52 r p q).
Proof. exact (eq_refl (term52 r p q)). Qed.
Lemma lem120387 (q : Prop) (r : Prop) (p : Prop) : ((term49 r p q) = (term50 r p)) = ((term49 r p q) = (term51 r p)).
Proof. exact (MK_COMB (@lem120386 r p q) (@lem120385 r p)). Qed.
Lemma lem120388 (q : Prop) (r : Prop) (p : Prop) : (term49 r p q) = (term53 q r p).
Proof. exact (eq_refl (term49 r p q)). Qed.
Lemma lem120389 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem120390 (q : Prop) (r : Prop) (p : Prop) : (term52 r p q) = (term54 q r p).
Proof. exact (MK_COMB (@lem120389) (@lem120388 q r p)). Qed.
Lemma lem120391 (r : Prop) (p : Prop) : (term51 r p) = (term51 r p).
Proof. exact (eq_refl (term51 r p)). Qed.
Lemma lem120392 (q : Prop) (r : Prop) (p : Prop) : ((term49 r p q) = (term51 r p)) = ((term53 q r p) = (term51 r p)).
Proof. exact (MK_COMB (@lem120390 q r p) (@lem120391 r p)). Qed.
Lemma lem120393 (q : Prop) (r : Prop) (p : Prop) : ((term49 r p q) = (term50 r p)) = ((term53 q r p) = (term51 r p)).
Proof. exact (TRANS (@lem120387 q r p) (@lem120392 q r p)). Qed.
Lemma lem120394 (r : Prop) (p : Prop) (q : Prop) (h1 : q = True) : (term53 q r p) = (term51 r p).
Proof. exact (EQ_MP (@lem120393 q r p) (@lem120384 r p q h1)). Qed.
Lemma lem120395 (r : Prop) (p : Prop) (q : Prop) (h1 : q = True) : (term51 r p) = (term53 q r p).
Proof. exact (SYM (@lem120394 r p q h1)). Qed.
Lemma lem120396 (r : Prop) (p : Prop) : (term48 r p) = (term48 r p).
Proof. exact (eq_refl (term48 r p)). Qed.
Lemma lem120397 (r : Prop) (p : Prop) (q : Prop) (h1 : q = False) : (term49 r p q) = (term55 r p).
Proof. exact (MK_COMB (@lem120396 r p) (@lem120368 q h1)). Qed.
Lemma lem120398 (r : Prop) (p : Prop) : (term55 r p) = (term56 r p).
Proof. exact (eq_refl (term55 r p)). Qed.
Lemma lem120399 (r : Prop) (p : Prop) (q : Prop) : (term52 r p q) = (term52 r p q).
Proof. exact (eq_refl (term52 r p q)). Qed.
Lemma lem120400 (q : Prop) (r : Prop) (p : Prop) : ((term49 r p q) = (term55 r p)) = ((term49 r p q) = (term56 r p)).
Proof. exact (MK_COMB (@lem120399 r p q) (@lem120398 r p)). Qed.
Lemma lem120401 (q : Prop) (r : Prop) (p : Prop) : (term49 r p q) = (term53 q r p).
Proof. exact (eq_refl (term49 r p q)). Qed.
Lemma lem120402 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem120403 (q : Prop) (r : Prop) (p : Prop) : (term52 r p q) = (term54 q r p).
Proof. exact (MK_COMB (@lem120402) (@lem120401 q r p)). Qed.
Lemma lem120404 (r : Prop) (p : Prop) : (term56 r p) = (term56 r p).
Proof. exact (eq_refl (term56 r p)). Qed.
Lemma lem120405 (q : Prop) (r : Prop) (p : Prop) : ((term49 r p q) = (term56 r p)) = ((term53 q r p) = (term56 r p)).
Proof. exact (MK_COMB (@lem120403 q r p) (@lem120404 r p)). Qed.
Lemma lem120406 (q : Prop) (r : Prop) (p : Prop) : ((term49 r p q) = (term55 r p)) = ((term53 q r p) = (term56 r p)).
Proof. exact (TRANS (@lem120400 q r p) (@lem120405 q r p)). Qed.
Lemma lem120407 (r : Prop) (p : Prop) (q : Prop) (h1 : q = False) : (term53 q r p) = (term56 r p).
Proof. exact (EQ_MP (@lem120406 q r p) (@lem120397 r p q h1)). Qed.
Lemma lem120408 (r : Prop) (p : Prop) (q : Prop) (h1 : q = False) : (term56 r p) = (term53 q r p).
Proof. exact (SYM (@lem120407 r p q h1)). Qed.
Lemma lem120412 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem120413 (r : Prop) : (term57 r) = (~ r).
Proof. exact (@lem120412 (~ r)). Qed.
Lemma lem120414 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem120415 (r : Prop) : (term58 r) = (term59 r).
Proof. exact (MK_COMB (@lem120414) (@lem120413 r)). Qed.
Lemma lem120423 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem120424 (p : Prop) : (p /\ True) = p.
Proof. exact (@lem120423 p). Qed.
Lemma lem120425 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem120426 (p : Prop) : (term60 p) = (@eq Prop p).
Proof. exact (MK_COMB (@lem120425) (@lem120424 p)). Qed.
Lemma lem120427 (r : Prop) : r = r.
Proof. exact (eq_refl r). Qed.
Lemma lem120428 (p : Prop) (r : Prop) : ((p /\ True) = r) = (p = r).
Proof. exact (MK_COMB (@lem120426 p) (@lem120427 r)). Qed.
Lemma lem120431 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem120432 (p : Prop) (r : Prop) : (term61 p r) = (term62 p r).
Proof. exact (MK_COMB (@lem120431) (@lem120428 p r)). Qed.
Lemma lem120433 (p : Prop) : (~ p) = (~ p).
Proof. exact (eq_refl (~ p)). Qed.
Lemma lem120434 (r : Prop) (p : Prop) : (term63 r p) = (term64 r p).
Proof. exact (MK_COMB (@lem120432 p r) (@lem120433 p)). Qed.
Lemma lem120439 (r : Prop) (p : Prop) : (term51 r p) = (term65 r p).
Proof. exact (MK_COMB (@lem120415 r) (@lem120434 r p)). Qed.
Lemma lem120442 (r : Prop) (p : Prop) : (term65 r p) = (term51 r p).
Proof. exact (SYM (@lem120439 r p)). Qed.
Lemma lem120443 (r : Prop) : term7 r.
Proof. exact (@lem9851 r). Qed.
Lemma lem120444 (r : Prop) : (term7 r) = (term8 r).
Proof. exact (eq_refl (term7 r)). Qed.
Lemma lem120445 (r : Prop) : term8 r.
Proof. exact (EQ_MP (@lem120444 r) (@lem120443 r)). Qed.
Lemma lem120446 (r : Prop) (h1 : r = True) : r = True.
Proof. exact (h1). Qed.
Lemma lem120447 (r : Prop) (h1 : r = False) : r = False.
Proof. exact (h1). Qed.
Lemma lem120458 (p : Prop) : (term66 p) = (term66 p).
Proof. exact (eq_refl (term66 p)). Qed.
Lemma lem120459 (p : Prop) (r : Prop) (h1 : r = True) : (term67 p r) = (term68 p).
Proof. exact (MK_COMB (@lem120458 p) (@lem120446 r h1)). Qed.
Lemma lem120460 (p : Prop) : (term68 p) = (term69 p).
Proof. exact (eq_refl (term68 p)). Qed.
Lemma lem120461 (p : Prop) (r : Prop) : (term70 p r) = (term70 p r).
Proof. exact (eq_refl (term70 p r)). Qed.
Lemma lem120462 (r : Prop) (p : Prop) : ((term67 p r) = (term68 p)) = ((term67 p r) = (term69 p)).
Proof. exact (MK_COMB (@lem120461 p r) (@lem120460 p)). Qed.
Lemma lem120463 (r : Prop) (p : Prop) : (term67 p r) = (term65 r p).
Proof. exact (eq_refl (term67 p r)). Qed.
Lemma lem120464 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem120465 (r : Prop) (p : Prop) : (term70 p r) = (term71 r p).
Proof. exact (MK_COMB (@lem120464) (@lem120463 r p)). Qed.
Lemma lem120466 (p : Prop) : (term69 p) = (term69 p).
Proof. exact (eq_refl (term69 p)). Qed.
Lemma lem120467 (r : Prop) (p : Prop) : ((term67 p r) = (term69 p)) = ((term65 r p) = (term69 p)).
Proof. exact (MK_COMB (@lem120465 r p) (@lem120466 p)). Qed.
Lemma lem120468 (r : Prop) (p : Prop) : ((term67 p r) = (term68 p)) = ((term65 r p) = (term69 p)).
Proof. exact (TRANS (@lem120462 r p) (@lem120467 r p)). Qed.
Lemma lem120469 (p : Prop) (r : Prop) (h1 : r = True) : (term65 r p) = (term69 p).
Proof. exact (EQ_MP (@lem120468 r p) (@lem120459 p r h1)). Qed.
Lemma lem120470 (p : Prop) (r : Prop) (h1 : r = True) : (term69 p) = (term65 r p).
Proof. exact (SYM (@lem120469 p r h1)). Qed.
Lemma lem120471 (p : Prop) : (term66 p) = (term66 p).
Proof. exact (eq_refl (term66 p)). Qed.
Lemma lem120472 (p : Prop) (r : Prop) (h1 : r = False) : (term67 p r) = (term72 p).
Proof. exact (MK_COMB (@lem120471 p) (@lem120447 r h1)). Qed.
Lemma lem120473 (p : Prop) : (term72 p) = (term73 p).
Proof. exact (eq_refl (term72 p)). Qed.
Lemma lem120474 (p : Prop) (r : Prop) : (term70 p r) = (term70 p r).
Proof. exact (eq_refl (term70 p r)). Qed.
Lemma lem120475 (r : Prop) (p : Prop) : ((term67 p r) = (term72 p)) = ((term67 p r) = (term73 p)).
Proof. exact (MK_COMB (@lem120474 p r) (@lem120473 p)). Qed.
Lemma lem120476 (r : Prop) (p : Prop) : (term67 p r) = (term65 r p).
Proof. exact (eq_refl (term67 p r)). Qed.
Lemma lem120477 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem120478 (r : Prop) (p : Prop) : (term70 p r) = (term71 r p).
Proof. exact (MK_COMB (@lem120477) (@lem120476 r p)). Qed.
Lemma lem120479 (p : Prop) : (term73 p) = (term73 p).
Proof. exact (eq_refl (term73 p)). Qed.
Lemma lem120480 (r : Prop) (p : Prop) : ((term67 p r) = (term73 p)) = ((term65 r p) = (term73 p)).
Proof. exact (MK_COMB (@lem120478 r p) (@lem120479 p)). Qed.
Lemma lem120481 (r : Prop) (p : Prop) : ((term67 p r) = (term72 p)) = ((term65 r p) = (term73 p)).
Proof. exact (TRANS (@lem120475 r p) (@lem120480 r p)). Qed.
Lemma lem120482 (p : Prop) (r : Prop) (h1 : r = False) : (term65 r p) = (term73 p).
Proof. exact (EQ_MP (@lem120481 r p) (@lem120472 p r h1)). Qed.
Lemma lem120483 (p : Prop) (r : Prop) (h1 : r = False) : (term73 p) = (term65 r p).
Proof. exact (SYM (@lem120482 p r h1)). Qed.
Lemma lem120487 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem120488 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem120489 : term43 = (imp False).
Proof. exact (MK_COMB (@lem120488) (@lem120487)). Qed.
Lemma lem120495 (t : Prop) : (t = True) = t.
Proof. exact (proj1 (@lem1856 t)). Qed.
Lemma lem120496 (p : Prop) : (p = True) = p.
Proof. exact (@lem120495 p). Qed.
Lemma lem120497 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem120498 (p : Prop) : (term74 p) = (imp p).
Proof. exact (MK_COMB (@lem120497) (@lem120496 p)). Qed.
Lemma lem120499 (p : Prop) : (~ p) = (~ p).
Proof. exact (eq_refl (~ p)). Qed.
Lemma lem120500 (p : Prop) : (term75 p) = (term76 p).
Proof. exact (MK_COMB (@lem120498 p) (@lem120499 p)). Qed.
Lemma lem120503 (p : Prop) : (term69 p) = (term77 p).
Proof. exact (MK_COMB (@lem120489) (@lem120500 p)). Qed.
Lemma lem120505 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem120506 (p : Prop) : (term77 p) = True.
Proof. exact (@lem120505 (term76 p)). Qed.
Lemma lem120507 (p : Prop) : (term69 p) = True.
Proof. exact (TRANS (@lem120503 p) (@lem120506 p)). Qed.
Lemma lem120508 (p : Prop) : True = (term69 p).
Proof. exact (SYM (@lem120507 p)). Qed.
Lemma lem120509 (p : Prop) : term69 p.
Proof. exact (EQ_MP (@lem120508 p) (@lem0)). Qed.
Lemma lem120513 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem120514 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem120515 : term45 = (imp True).
Proof. exact (MK_COMB (@lem120514) (@lem120513)). Qed.
Lemma lem120521 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem120522 (p : Prop) : (p = False) = (~ p).
Proof. exact (@lem120521 p). Qed.
Lemma lem120523 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem120524 (p : Prop) : (term78 p) = (term59 p).
Proof. exact (MK_COMB (@lem120523) (@lem120522 p)). Qed.
Lemma lem120525 (p : Prop) : (~ p) = (~ p).
Proof. exact (eq_refl (~ p)). Qed.
Lemma lem120526 (p : Prop) : (term79 p) = (term80 p).
Proof. exact (MK_COMB (@lem120524 p) (@lem120525 p)). Qed.
Lemma lem120528 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem120529 (p : Prop) : (term80 p) = True.
Proof. exact (@lem120528 (~ p)). Qed.
Lemma lem120530 (p : Prop) : (term79 p) = True.
Proof. exact (TRANS (@lem120526 p) (@lem120529 p)). Qed.
Lemma lem120531 (p : Prop) : (term73 p) = (True -> True).
Proof. exact (MK_COMB (@lem120515) (@lem120530 p)). Qed.
Lemma lem120533 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem120534 : (True -> True) = True.
Proof. exact (@lem120533 True). Qed.
Lemma lem120535 (p : Prop) : (term73 p) = True.
Proof. exact (TRANS (@lem120531 p) (@lem120534)). Qed.
Lemma lem120536 (p : Prop) : True = (term73 p).
Proof. exact (SYM (@lem120535 p)). Qed.
Lemma lem120537 (p : Prop) : term73 p.
Proof. exact (EQ_MP (@lem120536 p) (@lem0)). Qed.
Lemma lem120538 (p : Prop) (r : Prop) (h1 : r = False) : term65 r p.
Proof. exact (EQ_MP (@lem120483 p r h1) (@lem120537 p)). Qed.
Lemma lem120539 (p : Prop) (r : Prop) (h1 : r = True) : term65 r p.
Proof. exact (EQ_MP (@lem120470 p r h1) (@lem120509 p)). Qed.
Lemma lem120541 (r : Prop) (p : Prop) : term65 r p.
Proof. exact (or_elim (@lem120445 r) (fun h0 : r = True => @lem120539 p r h0) (fun h0 : r = False => @lem120538 p r h0)). Qed.
Lemma lem120542 (r : Prop) (p : Prop) : term51 r p.
Proof. exact (EQ_MP (@lem120442 r p) (@lem120541 r p)). Qed.
Lemma lem120546 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem120547 (r : Prop) : (term81 r) = False.
Proof. exact (@lem120546 (~ r)). Qed.
Lemma lem120548 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem120549 (r : Prop) : (term82 r) = (imp False).
Proof. exact (MK_COMB (@lem120548) (@lem120547 r)). Qed.
Lemma lem120557 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem120558 (p : Prop) : (p /\ False) = False.
Proof. exact (@lem120557 p). Qed.
Lemma lem120559 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem120560 (p : Prop) : (term83 p) = (@eq Prop False).
Proof. exact (MK_COMB (@lem120559) (@lem120558 p)). Qed.
Lemma lem120561 (r : Prop) : r = r.
Proof. exact (eq_refl r). Qed.
Lemma lem120562 (p : Prop) (r : Prop) : ((p /\ False) = r) = (False = r).
Proof. exact (MK_COMB (@lem120560 p) (@lem120561 r)). Qed.
Lemma lem120564 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem120565 (r : Prop) : (False = r) = (~ r).
Proof. exact (@lem120564 r). Qed.
Lemma lem120566 (p : Prop) (r : Prop) : ((p /\ False) = r) = (~ r).
Proof. exact (TRANS (@lem120562 p r) (@lem120565 r)). Qed.
Lemma lem120567 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem120568 (p : Prop) (r : Prop) : (term84 p r) = (term59 r).
Proof. exact (MK_COMB (@lem120567) (@lem120566 p r)). Qed.
Lemma lem120569 (p : Prop) : (~ p) = (~ p).
Proof. exact (eq_refl (~ p)). Qed.
Lemma lem120570 (r : Prop) (p : Prop) : (term85 r p) = (term86 r p).
Proof. exact (MK_COMB (@lem120568 p r) (@lem120569 p)). Qed.
Lemma lem120573 (r : Prop) (p : Prop) : (term56 r p) = (term87 r p).
Proof. exact (MK_COMB (@lem120549 r) (@lem120570 r p)). Qed.
Lemma lem120575 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem120576 (r : Prop) (p : Prop) : (term87 r p) = True.
Proof. exact (@lem120575 (term86 r p)). Qed.
Lemma lem120577 (r : Prop) (p : Prop) : (term56 r p) = True.
Proof. exact (TRANS (@lem120573 r p) (@lem120576 r p)). Qed.
Lemma lem120578 (r : Prop) (p : Prop) : True = (term56 r p).
Proof. exact (SYM (@lem120577 r p)). Qed.
Lemma lem120579 (r : Prop) (p : Prop) : term56 r p.
Proof. exact (EQ_MP (@lem120578 r p) (@lem0)). Qed.
Lemma lem120580 (r : Prop) (p : Prop) (q : Prop) (h1 : q = False) : term53 q r p.
Proof. exact (EQ_MP (@lem120408 r p q h1) (@lem120579 r p)). Qed.
Lemma lem120581 (r : Prop) (p : Prop) (q : Prop) (h1 : q = True) : term53 q r p.
Proof. exact (EQ_MP (@lem120395 r p q h1) (@lem120542 r p)). Qed.
Lemma lem120584 (q : Prop) (r : Prop) (p : Prop) : term53 q r p.
Proof. exact (or_elim (@lem120366 q) (fun h0 : q = True => @lem120581 r p q h0) (fun h0 : q = False => @lem120580 r p q h0)). Qed.
Lemma lem120585 (q : Prop) (r : Prop) (p : Prop) (h1 : term53 q r p) : term53 q r p.
Proof. exact (h1). Qed.
Lemma lem120586 (q : Prop) (r : Prop) (h1 : term88 q r) : term88 q r.
Proof. exact (h1). Qed.
Lemma lem120587 (q : Prop) (r : Prop) (p : Prop) (h1 : term88 q r) (h2 : term53 q r p) : term89 q r p.
Proof. exact (@lem120585 q r p h2 (@lem120586 q r h1)). Qed.
Lemma lem120588 (p : Prop) (q : Prop) (r : Prop) (h1 : term88 q r) : term90 q r p.
Proof. exact (fun h0 : term53 q r p => @lem120587 q r p h1 h0). Qed.
Lemma lem120589 (q : Prop) (r : Prop) (p : Prop) (h1 : term53 q r p) : term53 q r p.
Proof. exact (h1). Qed.
Lemma lem120590 (q : Prop) (r : Prop) (p : Prop) (h1 : term88 q r) (h2 : term53 q r p) : term89 q r p.
Proof. exact (@lem120588 p q r h1 (@lem120589 q r p h2)). Qed.
Lemma lem120591 (q : Prop) (r : Prop) (p : Prop) (h1 : term53 q r p) : term53 q r p.
Proof. exact (fun h0 : term88 q r => @lem120590 q r p h0 h1). Qed.
Lemma lem120592 (q : Prop) (r : Prop) (p : Prop) : term91 q r p.
Proof. exact (fun h0 : term53 q r p => @lem120591 q r p h0). Qed.
Lemma lem120594 (P : nat -> Prop) : term92 P.
Proof. exact (@lem117739 P). Qed.
Lemma lem120595 (P : nat -> Prop) : (term92 P) = ((term93 P) = (term94 P)).
Proof. exact (eq_refl (term92 P)). Qed.
Lemma lem120608 (p : Prop) : p = (term42 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem120609 {_9099 : Type'} (P : _9099 -> Prop) : ((term95 _9099 P) = (term96 _9099 P)) = (term97 _9099 P).
Proof. exact (@lem120608 ((term95 _9099 P) = (term96 _9099 P))). Qed.
Lemma lem120610 {_9099 : Type'} (P : _9099 -> Prop) : (term97 _9099 P) = ((term95 _9099 P) = (term96 _9099 P)).
Proof. exact (SYM (@lem120609 _9099 P)). Qed.
Lemma lem120611 {_9099 : Type'} (P : _9099 -> Prop) (h1 : term98 _9099 P) : term98 _9099 P.
Proof. exact (h1). Qed.
Lemma lem120614 {_9099 : Type'} (P : _9099 -> Prop) (h1 : term97 _9099 P) : term97 _9099 P.
Proof. exact (h1). Qed.
Lemma lem120615 {_9099 : Type'} (P : _9099 -> Prop) : term99 _9099 P.
Proof. exact (fun h0 : term97 _9099 P => @lem120614 _9099 P h0). Qed.
Lemma lem120616 {_9099 : Type'} (P : _9099 -> Prop) (h1 : term99 _9099 P) : term99 _9099 P.
Proof. exact (h1). Qed.
Lemma lem120617 {_9099 : Type'} (P : _9099 -> Prop) (h1 : term97 _9099 P) : term97 _9099 P.
Proof. exact (h1). Qed.
Lemma lem120618 {_9099 : Type'} (P : _9099 -> Prop) (h1 : term97 _9099 P) (h2 : term99 _9099 P) : term97 _9099 P.
Proof. exact (@lem120616 _9099 P h2 (@lem120617 _9099 P h1)). Qed.
Lemma lem120619 {_9099 : Type'} (P : _9099 -> Prop) (h1 : term97 _9099 P) : term100 _9099 P.
Proof. exact (fun h0 : term99 _9099 P => @lem120618 _9099 P h1 h0). Qed.
Lemma lem120620 {_9099 : Type'} (P : _9099 -> Prop) (h1 : term99 _9099 P) : term99 _9099 P.
Proof. exact (h1). Qed.
Lemma lem120621 {_9099 : Type'} (P : _9099 -> Prop) (h1 : term97 _9099 P) (h2 : term99 _9099 P) : term97 _9099 P.
Proof. exact (@lem120619 _9099 P h1 (@lem120620 _9099 P h2)). Qed.
Lemma lem120622 {_9099 : Type'} (P : _9099 -> Prop) (h1 : term99 _9099 P) : term99 _9099 P.
Proof. exact (fun h0 : term97 _9099 P => @lem120621 _9099 P h0 h1). Qed.
Lemma lem120623 {_9099 : Type'} (P : _9099 -> Prop) : term101 _9099 P.
Proof. exact (fun h0 : term99 _9099 P => @lem120622 _9099 P h0). Qed.
Lemma lem120626 {_9099 : Type'} (P : _9099 -> Prop) : term99 _9099 P.
Proof. exact (@lem120623 _9099 P (@lem120615 _9099 P)). Qed.
Lemma lem120627 {_9099 : Type'} (P : _9099 -> Prop) : term99 _9099 P.
Proof. exact (@lem120626 _9099 P). Qed.
Lemma lem120633 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem120634 {_9099 : Type'} (P : _9099 -> Prop) : (term97 _9099 P) = (term102 _9099 P).
Proof. exact (@lem120633 (term98 _9099 P)). Qed.
Lemma lem120636 (t : Prop) : (term47 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem120637 {_9099 : Type'} (P : _9099 -> Prop) : (term102 _9099 P) = ((term95 _9099 P) = (term96 _9099 P)).
Proof. exact (@lem120636 ((term95 _9099 P) = (term96 _9099 P))). Qed.
Lemma lem120638 {_9099 : Type'} (P : _9099 -> Prop) : (term97 _9099 P) = ((term95 _9099 P) = (term96 _9099 P)).
Proof. exact (TRANS (@lem120634 _9099 P) (@lem120637 _9099 P)). Qed.
Lemma lem120647 {_9099 : Type'} : (term103 _9099) = (term104 _9099).
Proof. exact (fun_ext (fun P : _9099 -> Prop => @lem120638 _9099 P)). Qed.
Lemma lem120648 {_9099 : Type'} : (@all (_9099 -> Prop)) = (@all (_9099 -> Prop)).
Proof. exact (eq_refl (@all (_9099 -> Prop))). Qed.
Lemma lem120657 {_9099 : Type'} : (term105 _9099) = (term106 _9099).
Proof. exact (MK_COMB (@lem120648 _9099) (@lem120647 _9099)). Qed.
Lemma lem120660 {_9099 : Type'} (P : _9099 -> Prop) (x : _9099) : (term107 _9099 P x) = (term107 _9099 P x).
Proof. exact (eq_refl (term107 _9099 P x)). Qed.
Lemma lem120661 {_9099 : Type'} (P : _9099 -> Prop) : (term108 _9099 P) = (term108 _9099 P).
Proof. exact (fun_ext (fun x : _9099 => @lem120660 _9099 P x)). Qed.
Lemma lem120662 {_9099 : Type'} : (@ex _9099) = (@ex _9099).
Proof. exact (eq_refl (@ex _9099)). Qed.
Lemma lem120663 {_9099 : Type'} (P : _9099 -> Prop) : (term109 _9099 P) = (term109 _9099 P).
Proof. exact (MK_COMB (@lem120662 _9099) (@lem120661 _9099 P)). Qed.
Lemma lem120664 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem120665 {_9099 : Type'} (P : _9099 -> Prop) : (term96 _9099 P) = (term96 _9099 P).
Proof. exact (MK_COMB (@lem120664) (@lem120663 _9099 P)). Qed.
Lemma lem120666 {_9099 : Type'} (P : _9099 -> Prop) (x : _9099) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem120667 {_9099 : Type'} (P : _9099 -> Prop) : (term110 _9099 P) = (term110 _9099 P).
Proof. exact (fun_ext (fun x : _9099 => @lem120666 _9099 P x)). Qed.
Lemma lem120668 {_9099 : Type'} : (@all _9099) = (@all _9099).
Proof. exact (eq_refl (@all _9099)). Qed.
Lemma lem120669 {_9099 : Type'} (P : _9099 -> Prop) : (term95 _9099 P) = (term95 _9099 P).
Proof. exact (MK_COMB (@lem120668 _9099) (@lem120667 _9099 P)). Qed.
Lemma lem120670 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem120671 {_9099 : Type'} (P : _9099 -> Prop) : (term111 _9099 P) = (term111 _9099 P).
Proof. exact (MK_COMB (@lem120670) (@lem120669 _9099 P)). Qed.
Lemma lem120672 {_9099 : Type'} (P : _9099 -> Prop) : ((term95 _9099 P) = (term96 _9099 P)) = ((term95 _9099 P) = (term96 _9099 P)).
Proof. exact (MK_COMB (@lem120671 _9099 P) (@lem120665 _9099 P)). Qed.
Lemma lem120673 {_9099 : Type'} : (term104 _9099) = (term104 _9099).
Proof. exact (fun_ext (fun P : _9099 -> Prop => @lem120672 _9099 P)). Qed.
Lemma lem120674 {_9099 : Type'} : (@all (_9099 -> Prop)) = (@all (_9099 -> Prop)).
Proof. exact (eq_refl (@all (_9099 -> Prop))). Qed.
Lemma lem120675 {_9099 : Type'} : (term106 _9099) = (term106 _9099).
Proof. exact (MK_COMB (@lem120674 _9099) (@lem120673 _9099)). Qed.
Lemma lem120696 {_9099 : Type'} : (term105 _9099) = (term106 _9099).
Proof. exact (TRANS (@lem120657 _9099) (@lem120675 _9099)). Qed.
Lemma lem120697 {_9099 : Type'} : (term106 _9099) = (term105 _9099).
Proof. exact (SYM (@lem120696 _9099)). Qed.
Lemma lem120699 (p : Prop) : p = (term42 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem120700 {_9099 : Type'} (P : _9099 -> Prop) : ((term95 _9099 P) = (term96 _9099 P)) = (term97 _9099 P).
Proof. exact (@lem120699 ((term95 _9099 P) = (term96 _9099 P))). Qed.
Lemma lem120701 {_9099 : Type'} (P : _9099 -> Prop) : (term97 _9099 P) = ((term95 _9099 P) = (term96 _9099 P)).
Proof. exact (SYM (@lem120700 _9099 P)). Qed.
Lemma lem120702 {_9099 : Type'} (P : _9099 -> Prop) (h1 : term98 _9099 P) : term98 _9099 P.
Proof. exact (h1). Qed.
Lemma lem120704 {_9099 : Type'} (P : _9099 -> Prop) (x : _9099) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem120705 {_9099 : Type'} (P : _9099 -> Prop) : (term112 _9099 P) = (term109 _9099 P).
Proof. exact (@lem18392 _9099 P). Qed.
Lemma lem120706 {_9099 : Type'} (P : _9099 -> Prop) : (term113 _9099 P) = (term114 _9099 P).
Proof. exact (@lem120705 _9099 (term110 _9099 P)). Qed.
Lemma lem120707 {_9099 : Type'} (P : _9099 -> Prop) (x : _9099) : (term115 _9099 P x) = (P x).
Proof. exact (eq_refl (term115 _9099 P x)). Qed.
Lemma lem120708 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem120710 {_9099 : Type'} (P : _9099 -> Prop) (x : _9099) : (term116 _9099 P x) = (term107 _9099 P x).
Proof. exact (MK_COMB (@lem120708) (@lem120707 _9099 P x)). Qed.
Lemma lem120711 {_9099 : Type'} (P : _9099 -> Prop) : (term117 _9099 P) = (term108 _9099 P).
Proof. exact (fun_ext (fun x : _9099 => @lem120710 _9099 P x)). Qed.
Lemma lem120712 {_9099 : Type'} : (@ex _9099) = (@ex _9099).
Proof. exact (eq_refl (@ex _9099)). Qed.
Lemma lem120713 {_9099 : Type'} (P : _9099 -> Prop) : (term114 _9099 P) = (term109 _9099 P).
Proof. exact (MK_COMB (@lem120712 _9099) (@lem120711 _9099 P)). Qed.
Lemma lem120714 {_9099 : Type'} (P : _9099 -> Prop) : (term113 _9099 P) = (term109 _9099 P).
Proof. exact (TRANS (@lem120706 _9099 P) (@lem120713 _9099 P)). Qed.
Lemma lem120715 {_9099 : Type'} (P : _9099 -> Prop) : (term110 _9099 P) = (term110 _9099 P).
Proof. exact (fun_ext (fun x : _9099 => @lem120704 _9099 P x)). Qed.
Lemma lem120716 {_9099 : Type'} : (@all _9099) = (@all _9099).
Proof. exact (eq_refl (@all _9099)). Qed.
Lemma lem120717 {_9099 : Type'} (P : _9099 -> Prop) : (term95 _9099 P) = (term95 _9099 P).
Proof. exact (MK_COMB (@lem120716 _9099) (@lem120715 _9099 P)). Qed.
Lemma lem120718 {_9099 : Type'} (P : _9099 -> Prop) (x : _9099) : (term107 _9099 P x) = (term107 _9099 P x).
Proof. exact (eq_refl (term107 _9099 P x)). Qed.
Lemma lem120721 {_9099 : Type'} (P : _9099 -> Prop) (x : _9099) : (term118 _9099 P x) = (P x).
Proof. exact (@lem16933 (P x)). Qed.
Lemma lem120722 {_9099 : Type'} (P : _9099 -> Prop) : (term119 _9099 P) = (term31 _9099 P).
Proof. exact (@lem18394 _9099 P). Qed.
Lemma lem120723 {_9099 : Type'} (P : _9099 -> Prop) : (term96 _9099 P) = (term120 _9099 P).
Proof. exact (@lem120722 _9099 (term108 _9099 P)). Qed.
Lemma lem120724 {_9099 : Type'} (P : _9099 -> Prop) (x : _9099) : (term121 _9099 P x) = (term107 _9099 P x).
Proof. exact (eq_refl (term121 _9099 P x)). Qed.
Lemma lem120725 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem120726 {_9099 : Type'} (P : _9099 -> Prop) (x : _9099) : (term122 _9099 P x) = (term118 _9099 P x).
Proof. exact (MK_COMB (@lem120725) (@lem120724 _9099 P x)). Qed.
Lemma lem120727 {_9099 : Type'} (P : _9099 -> Prop) (x : _9099) : (term122 _9099 P x) = (P x).
Proof. exact (TRANS (@lem120726 _9099 P x) (@lem120721 _9099 P x)). Qed.
Lemma lem120728 {_9099 : Type'} (P : _9099 -> Prop) : (term123 _9099 P) = (term110 _9099 P).
Proof. exact (fun_ext (fun x : _9099 => @lem120727 _9099 P x)). Qed.
Lemma lem120729 {_9099 : Type'} : (@all _9099) = (@all _9099).
Proof. exact (eq_refl (@all _9099)). Qed.
Lemma lem120730 {_9099 : Type'} (P : _9099 -> Prop) : (term120 _9099 P) = (term95 _9099 P).
Proof. exact (MK_COMB (@lem120729 _9099) (@lem120728 _9099 P)). Qed.
Lemma lem120731 {_9099 : Type'} (P : _9099 -> Prop) : (term96 _9099 P) = (term95 _9099 P).
Proof. exact (TRANS (@lem120723 _9099 P) (@lem120730 _9099 P)). Qed.
Lemma lem120732 {_9099 : Type'} (P : _9099 -> Prop) : (term108 _9099 P) = (term108 _9099 P).
Proof. exact (fun_ext (fun x : _9099 => @lem120718 _9099 P x)). Qed.
Lemma lem120733 {_9099 : Type'} : (@ex _9099) = (@ex _9099).
Proof. exact (eq_refl (@ex _9099)). Qed.
Lemma lem120734 {_9099 : Type'} (P : _9099 -> Prop) : (term109 _9099 P) = (term109 _9099 P).
Proof. exact (MK_COMB (@lem120733 _9099) (@lem120732 _9099 P)). Qed.
Lemma lem120735 {_9099 : Type'} (P : _9099 -> Prop) : (term124 _9099 P) = (term109 _9099 P).
Proof. exact (@lem16933 (term109 _9099 P)). Qed.
Lemma lem120736 {_9099 : Type'} (P : _9099 -> Prop) : (term124 _9099 P) = (term109 _9099 P).
Proof. exact (TRANS (@lem120735 _9099 P) (@lem120734 _9099 P)). Qed.
Lemma lem120737 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem120738 {_9099 : Type'} (P : _9099 -> Prop) : (term125 _9099 P) = (term126 _9099 P).
Proof. exact (MK_COMB (@lem120737) (@lem120714 _9099 P)). Qed.
Lemma lem120739 {_9099 : Type'} (P : _9099 -> Prop) : (term127 _9099 P) = (term128 _9099 P).
Proof. exact (MK_COMB (@lem120738 _9099 P) (@lem120731 _9099 P)). Qed.
Lemma lem120740 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem120741 {_9099 : Type'} (P : _9099 -> Prop) : (term129 _9099 P) = (term129 _9099 P).
Proof. exact (MK_COMB (@lem120740) (@lem120717 _9099 P)). Qed.
Lemma lem120742 {_9099 : Type'} (P : _9099 -> Prop) : (term130 _9099 P) = (term131 _9099 P).
Proof. exact (MK_COMB (@lem120741 _9099 P) (@lem120736 _9099 P)). Qed.
Lemma lem120743 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem120744 {_9099 : Type'} (P : _9099 -> Prop) : (term132 _9099 P) = (term133 _9099 P).
Proof. exact (MK_COMB (@lem120743) (@lem120742 _9099 P)). Qed.
Lemma lem120745 {_9099 : Type'} (P : _9099 -> Prop) : (term134 _9099 P) = (term135 _9099 P).
Proof. exact (MK_COMB (@lem120744 _9099 P) (@lem120739 _9099 P)). Qed.
Lemma lem120746 {_9099 : Type'} (P : _9099 -> Prop) : (term98 _9099 P) = (term134 _9099 P).
Proof. exact (@lem17646 (term95 _9099 P) (term96 _9099 P)). Qed.
Lemma lem120747 {_9099 : Type'} (P : _9099 -> Prop) : (term98 _9099 P) = (term135 _9099 P).
Proof. exact (TRANS (@lem120746 _9099 P) (@lem120745 _9099 P)). Qed.
Lemma lem120766 {A : Type'} (P : Prop) (Q : A -> Prop) : (term136 A P Q) = (term137 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem120767 {_9099 : Type'} (P : Prop) (Q : _9099 -> Prop) : (term136 _9099 P Q) = (term137 _9099 P Q).
Proof. exact (@lem120766 _9099 P Q). Qed.
Lemma lem120768 {_9099 : Type'} (P : _9099 -> Prop) : (term138 _9099 P) = (term139 _9099 P).
Proof. exact (@lem120767 _9099 (term95 _9099 P) (term108 _9099 P)). Qed.
Lemma lem120769 {_9099 : Type'} (P : _9099 -> Prop) (x : _9099) : (term121 _9099 P x) = (term107 _9099 P x).
Proof. exact (eq_refl (term121 _9099 P x)). Qed.
Lemma lem120770 {_9099 : Type'} (P : _9099 -> Prop) : (term140 _9099 P) = (term108 _9099 P).
Proof. exact (fun_ext (fun x : _9099 => @lem120769 _9099 P x)). Qed.
Lemma lem120771 {_9099 : Type'} : (@ex _9099) = (@ex _9099).
Proof. exact (eq_refl (@ex _9099)). Qed.
Lemma lem120772 {_9099 : Type'} (P : _9099 -> Prop) : (term141 _9099 P) = (term109 _9099 P).
Proof. exact (MK_COMB (@lem120771 _9099) (@lem120770 _9099 P)). Qed.
Lemma lem120773 {_9099 : Type'} (P : _9099 -> Prop) : (term129 _9099 P) = (term129 _9099 P).
Proof. exact (eq_refl (term129 _9099 P)). Qed.
Lemma lem120774 {_9099 : Type'} (P : _9099 -> Prop) : (term138 _9099 P) = (term131 _9099 P).
Proof. exact (MK_COMB (@lem120773 _9099 P) (@lem120772 _9099 P)). Qed.
Lemma lem120775 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem120776 {_9099 : Type'} (P : _9099 -> Prop) : (term142 _9099 P) = (term143 _9099 P).
Proof. exact (MK_COMB (@lem120775) (@lem120774 _9099 P)). Qed.
Lemma lem120777 {_9099 : Type'} (P : _9099 -> Prop) (x : _9099) : (term121 _9099 P x) = (term107 _9099 P x).
Proof. exact (eq_refl (term121 _9099 P x)). Qed.
Lemma lem120778 {_9099 : Type'} (P : _9099 -> Prop) : (term129 _9099 P) = (term129 _9099 P).
Proof. exact (eq_refl (term129 _9099 P)). Qed.
Lemma lem120779 {_9099 : Type'} (P : _9099 -> Prop) (x : _9099) : (term144 _9099 P x) = (term145 _9099 P x).
Proof. exact (MK_COMB (@lem120778 _9099 P) (@lem120777 _9099 P x)). Qed.
Lemma lem120780 {_9099 : Type'} (P : _9099 -> Prop) : (term146 _9099 P) = (term147 _9099 P).
Proof. exact (fun_ext (fun x : _9099 => @lem120779 _9099 P x)). Qed.
Lemma lem120781 {_9099 : Type'} : (@ex _9099) = (@ex _9099).
Proof. exact (eq_refl (@ex _9099)). Qed.
Lemma lem120782 {_9099 : Type'} (P : _9099 -> Prop) : (term139 _9099 P) = (term148 _9099 P).
Proof. exact (MK_COMB (@lem120781 _9099) (@lem120780 _9099 P)). Qed.
Lemma lem120783 {_9099 : Type'} (P : _9099 -> Prop) : ((term138 _9099 P) = (term139 _9099 P)) = ((term131 _9099 P) = (term148 _9099 P)).
Proof. exact (MK_COMB (@lem120776 _9099 P) (@lem120782 _9099 P)). Qed.
Lemma lem120784 {_9099 : Type'} (P : _9099 -> Prop) : (term131 _9099 P) = (term148 _9099 P).
Proof. exact (EQ_MP (@lem120783 _9099 P) (@lem120768 _9099 P)). Qed.
Lemma lem120785 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem120786 {_9099 : Type'} (P : _9099 -> Prop) : (term133 _9099 P) = (term149 _9099 P).
Proof. exact (MK_COMB (@lem120785) (@lem120784 _9099 P)). Qed.
Lemma lem120788 {A : Type'} (P : A -> Prop) (Q : Prop) : (term150 A P Q) = (term151 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem120789 {_9099 : Type'} (P : _9099 -> Prop) (Q : Prop) : (term150 _9099 P Q) = (term151 _9099 P Q).
Proof. exact (@lem120788 _9099 P Q). Qed.
Lemma lem120790 {_9099 : Type'} (P : _9099 -> Prop) : (term152 _9099 P) = (term153 _9099 P).
Proof. exact (@lem120789 _9099 (term108 _9099 P) (term95 _9099 P)). Qed.
Lemma lem120791 {_9099 : Type'} (P : _9099 -> Prop) (x : _9099) : (term121 _9099 P x) = (term107 _9099 P x).
Proof. exact (eq_refl (term121 _9099 P x)). Qed.
Lemma lem120792 {_9099 : Type'} (P : _9099 -> Prop) : (term140 _9099 P) = (term108 _9099 P).
Proof. exact (fun_ext (fun x : _9099 => @lem120791 _9099 P x)). Qed.
Lemma lem120793 {_9099 : Type'} : (@ex _9099) = (@ex _9099).
Proof. exact (eq_refl (@ex _9099)). Qed.
Lemma lem120794 {_9099 : Type'} (P : _9099 -> Prop) : (term141 _9099 P) = (term109 _9099 P).
Proof. exact (MK_COMB (@lem120793 _9099) (@lem120792 _9099 P)). Qed.
Lemma lem120795 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem120796 {_9099 : Type'} (P : _9099 -> Prop) : (term154 _9099 P) = (term126 _9099 P).
Proof. exact (MK_COMB (@lem120795) (@lem120794 _9099 P)). Qed.
Lemma lem120797 {_9099 : Type'} (P : _9099 -> Prop) : (term95 _9099 P) = (term95 _9099 P).
Proof. exact (eq_refl (term95 _9099 P)). Qed.
Lemma lem120798 {_9099 : Type'} (P : _9099 -> Prop) : (term152 _9099 P) = (term128 _9099 P).
Proof. exact (MK_COMB (@lem120796 _9099 P) (@lem120797 _9099 P)). Qed.
Lemma lem120799 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem120800 {_9099 : Type'} (P : _9099 -> Prop) : (term155 _9099 P) = (term156 _9099 P).
Proof. exact (MK_COMB (@lem120799) (@lem120798 _9099 P)). Qed.
Lemma lem120801 {_9099 : Type'} (P : _9099 -> Prop) (x : _9099) : (term121 _9099 P x) = (term107 _9099 P x).
Proof. exact (eq_refl (term121 _9099 P x)). Qed.
Lemma lem120802 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem120803 {_9099 : Type'} (P : _9099 -> Prop) (x : _9099) : (term157 _9099 P x) = (term158 _9099 P x).
Proof. exact (MK_COMB (@lem120802) (@lem120801 _9099 P x)). Qed.
Lemma lem120804 {_9099 : Type'} (P : _9099 -> Prop) : (term95 _9099 P) = (term95 _9099 P).
Proof. exact (eq_refl (term95 _9099 P)). Qed.
Lemma lem120805 {_9099 : Type'} (x : _9099) (P : _9099 -> Prop) : (term159 _9099 x P) = (term160 _9099 x P).
Proof. exact (MK_COMB (@lem120803 _9099 P x) (@lem120804 _9099 P)). Qed.
Lemma lem120806 {_9099 : Type'} (P : _9099 -> Prop) : (term161 _9099 P) = (term162 _9099 P).
Proof. exact (fun_ext (fun x : _9099 => @lem120805 _9099 x P)). Qed.
Lemma lem120807 {_9099 : Type'} : (@ex _9099) = (@ex _9099).
Proof. exact (eq_refl (@ex _9099)). Qed.
Lemma lem120808 {_9099 : Type'} (P : _9099 -> Prop) : (term153 _9099 P) = (term163 _9099 P).
Proof. exact (MK_COMB (@lem120807 _9099) (@lem120806 _9099 P)). Qed.
Lemma lem120809 {_9099 : Type'} (P : _9099 -> Prop) : ((term152 _9099 P) = (term153 _9099 P)) = ((term128 _9099 P) = (term163 _9099 P)).
Proof. exact (MK_COMB (@lem120800 _9099 P) (@lem120808 _9099 P)). Qed.
Lemma lem120810 {_9099 : Type'} (P : _9099 -> Prop) : (term128 _9099 P) = (term163 _9099 P).
Proof. exact (EQ_MP (@lem120809 _9099 P) (@lem120790 _9099 P)). Qed.
Lemma lem120811 {_9099 : Type'} (P : _9099 -> Prop) : (term135 _9099 P) = (term164 _9099 P).
Proof. exact (MK_COMB (@lem120786 _9099 P) (@lem120810 _9099 P)). Qed.
Lemma lem120813 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term165 A P Q) = (term166 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem120814 {_9099 : Type'} (P : _9099 -> Prop) (Q : _9099 -> Prop) : (term165 _9099 P Q) = (term166 _9099 P Q).
Proof. exact (@lem120813 _9099 P Q). Qed.
Lemma lem120815 {_9099 : Type'} (P : _9099 -> Prop) : (term167 _9099 P) = (term168 _9099 P).
Proof. exact (@lem120814 _9099 (term147 _9099 P) (term162 _9099 P)). Qed.
Lemma lem120816 {_9099 : Type'} (P : _9099 -> Prop) (x : _9099) : (term169 _9099 P x) = (term145 _9099 P x).
Proof. exact (eq_refl (term169 _9099 P x)). Qed.
Lemma lem120817 {_9099 : Type'} (P : _9099 -> Prop) : (term170 _9099 P) = (term147 _9099 P).
Proof. exact (fun_ext (fun x : _9099 => @lem120816 _9099 P x)). Qed.
Lemma lem120818 {_9099 : Type'} : (@ex _9099) = (@ex _9099).
Proof. exact (eq_refl (@ex _9099)). Qed.
Lemma lem120819 {_9099 : Type'} (P : _9099 -> Prop) : (term171 _9099 P) = (term148 _9099 P).
Proof. exact (MK_COMB (@lem120818 _9099) (@lem120817 _9099 P)). Qed.
Lemma lem120820 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem120821 {_9099 : Type'} (P : _9099 -> Prop) : (term172 _9099 P) = (term149 _9099 P).
Proof. exact (MK_COMB (@lem120820) (@lem120819 _9099 P)). Qed.
Lemma lem120822 {_9099 : Type'} (x : _9099) (P : _9099 -> Prop) : (term173 _9099 P x) = (term160 _9099 x P).
Proof. exact (eq_refl (term173 _9099 P x)). Qed.
Lemma lem120823 {_9099 : Type'} (P : _9099 -> Prop) : (term174 _9099 P) = (term162 _9099 P).
Proof. exact (fun_ext (fun x : _9099 => @lem120822 _9099 x P)). Qed.
Lemma lem120824 {_9099 : Type'} : (@ex _9099) = (@ex _9099).
Proof. exact (eq_refl (@ex _9099)). Qed.
Lemma lem120825 {_9099 : Type'} (P : _9099 -> Prop) : (term175 _9099 P) = (term163 _9099 P).
Proof. exact (MK_COMB (@lem120824 _9099) (@lem120823 _9099 P)). Qed.
Lemma lem120826 {_9099 : Type'} (P : _9099 -> Prop) : (term167 _9099 P) = (term164 _9099 P).
Proof. exact (MK_COMB (@lem120821 _9099 P) (@lem120825 _9099 P)). Qed.
Lemma lem120827 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem120828 {_9099 : Type'} (P : _9099 -> Prop) : (term176 _9099 P) = (term177 _9099 P).
Proof. exact (MK_COMB (@lem120827) (@lem120826 _9099 P)). Qed.
Lemma lem120829 {_9099 : Type'} (P : _9099 -> Prop) (x : _9099) : (term169 _9099 P x) = (term145 _9099 P x).
Proof. exact (eq_refl (term169 _9099 P x)). Qed.
Lemma lem120830 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem120831 {_9099 : Type'} (P : _9099 -> Prop) (x : _9099) : (term178 _9099 P x) = (term179 _9099 P x).
Proof. exact (MK_COMB (@lem120830) (@lem120829 _9099 P x)). Qed.
Lemma lem120832 {_9099 : Type'} (x : _9099) (P : _9099 -> Prop) : (term173 _9099 P x) = (term160 _9099 x P).
Proof. exact (eq_refl (term173 _9099 P x)). Qed.
Lemma lem120833 {_9099 : Type'} (x : _9099) (P : _9099 -> Prop) : (term180 _9099 P x) = (term181 _9099 x P).
Proof. exact (MK_COMB (@lem120831 _9099 P x) (@lem120832 _9099 x P)). Qed.
Lemma lem120834 {_9099 : Type'} (P : _9099 -> Prop) : (term182 _9099 P) = (term183 _9099 P).
Proof. exact (fun_ext (fun x : _9099 => @lem120833 _9099 x P)). Qed.
Lemma lem120835 {_9099 : Type'} : (@ex _9099) = (@ex _9099).
Proof. exact (eq_refl (@ex _9099)). Qed.
Lemma lem120836 {_9099 : Type'} (P : _9099 -> Prop) : (term168 _9099 P) = (term184 _9099 P).
Proof. exact (MK_COMB (@lem120835 _9099) (@lem120834 _9099 P)). Qed.
Lemma lem120837 {_9099 : Type'} (P : _9099 -> Prop) : ((term167 _9099 P) = (term168 _9099 P)) = ((term164 _9099 P) = (term184 _9099 P)).
Proof. exact (MK_COMB (@lem120828 _9099 P) (@lem120836 _9099 P)). Qed.
Lemma lem120838 {_9099 : Type'} (P : _9099 -> Prop) : (term164 _9099 P) = (term184 _9099 P).
Proof. exact (EQ_MP (@lem120837 _9099 P) (@lem120815 _9099 P)). Qed.
Lemma lem120840 {_9099 : Type'} (P : _9099 -> Prop) : (term135 _9099 P) = (term184 _9099 P).
Proof. exact (TRANS (@lem120811 _9099 P) (@lem120838 _9099 P)). Qed.
Lemma lem120841 {_9099 : Type'} (P : _9099 -> Prop) : (term98 _9099 P) = (term184 _9099 P).
Proof. exact (TRANS (@lem120747 _9099 P) (@lem120840 _9099 P)). Qed.
Lemma lem120842 {_9099 : Type'} (P : _9099 -> Prop) (h1 : term98 _9099 P) : term184 _9099 P.
Proof. exact (EQ_MP (@lem120841 _9099 P) (@lem120702 _9099 P h1)). Qed.
Lemma lem120843 {_9099 : Type'} (x : _9099) (P : _9099 -> Prop) (h1 : term181 _9099 x P) : term181 _9099 x P.
Proof. exact (h1). Qed.
Lemma lem120846 {_9099 : Type'} (P : _9099 -> Prop) (x : _9099) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem120847 {_9099 : Type'} (P : _9099 -> Prop) : (term110 _9099 P) = (term110 _9099 P).
Proof. exact (fun_ext (fun x : _9099 => @lem120846 _9099 P x)). Qed.
Lemma lem120848 {_9099 : Type'} : (@all _9099) = (@all _9099).
Proof. exact (eq_refl (@all _9099)). Qed.
Lemma lem120849 {_9099 : Type'} (P : _9099 -> Prop) : (term95 _9099 P) = (term95 _9099 P).
Proof. exact (MK_COMB (@lem120848 _9099) (@lem120847 _9099 P)). Qed.
Lemma lem120856 {_9099 : Type'} (P : _9099 -> Prop) (x : _9099) : (term158 _9099 P x) = (term158 _9099 P x).
Proof. exact (eq_refl (term158 _9099 P x)). Qed.
Lemma lem120857 {_9099 : Type'} (x : _9099) (P : _9099 -> Prop) : (term160 _9099 x P) = (term160 _9099 x P).
Proof. exact (MK_COMB (@lem120856 _9099 P x) (@lem120849 _9099 P)). Qed.
Lemma lem120862 {_9099 : Type'} (P : _9099 -> Prop) (x : _9099) : (term107 _9099 P x) = (term107 _9099 P x).
Proof. exact (eq_refl (term107 _9099 P x)). Qed.
Lemma lem120865 {_9099 : Type'} (P : _9099 -> Prop) (x : _9099) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem120866 {_9099 : Type'} (P : _9099 -> Prop) : (term110 _9099 P) = (term110 _9099 P).
Proof. exact (fun_ext (fun x : _9099 => @lem120865 _9099 P x)). Qed.
Lemma lem120867 {_9099 : Type'} : (@all _9099) = (@all _9099).
Proof. exact (eq_refl (@all _9099)). Qed.
Lemma lem120868 {_9099 : Type'} (P : _9099 -> Prop) : (term95 _9099 P) = (term95 _9099 P).
Proof. exact (MK_COMB (@lem120867 _9099) (@lem120866 _9099 P)). Qed.
Lemma lem120869 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem120870 {_9099 : Type'} (P : _9099 -> Prop) : (term129 _9099 P) = (term129 _9099 P).
Proof. exact (MK_COMB (@lem120869) (@lem120868 _9099 P)). Qed.
Lemma lem120871 {_9099 : Type'} (P : _9099 -> Prop) (x : _9099) : (term145 _9099 P x) = (term145 _9099 P x).
Proof. exact (MK_COMB (@lem120870 _9099 P) (@lem120862 _9099 P x)). Qed.
Lemma lem120872 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem120873 {_9099 : Type'} (P : _9099 -> Prop) (x : _9099) : (term179 _9099 P x) = (term179 _9099 P x).
Proof. exact (MK_COMB (@lem120872) (@lem120871 _9099 P x)). Qed.
Lemma lem120874 {_9099 : Type'} (x : _9099) (P : _9099 -> Prop) : (term181 _9099 x P) = (term181 _9099 x P).
Proof. exact (MK_COMB (@lem120873 _9099 P x) (@lem120857 _9099 x P)). Qed.
Lemma lem120875 {_9099 : Type'} (x : _9099) (P : _9099 -> Prop) (h1 : term181 _9099 x P) : term181 _9099 x P.
Proof. exact (EQ_MP (@lem120874 _9099 x P) (@lem120843 _9099 x P h1)). Qed.
Lemma lem120876 {_9099 : Type'} (P : _9099 -> Prop) (x : _9099) (h1 : term145 _9099 P x) : term145 _9099 P x.
Proof. exact (h1). Qed.
Lemma lem120877 {_9099 : Type'} (x : _9099) (P : _9099 -> Prop) (h1 : term160 _9099 x P) : term160 _9099 x P.
Proof. exact (h1). Qed.
Lemma lem120879 {_9099 : Type'} (P : _9099 -> Prop) (x : _9099) (h1 : term145 _9099 P x) : term95 _9099 P.
Proof. exact (proj1 (@lem120876 _9099 P x h1)). Qed.
Lemma lem120880 {_9099 : Type'} (x : _9099) (P : _9099 -> Prop) (h1 : term160 _9099 x P) : term95 _9099 P.
Proof. exact (proj2 (@lem120877 _9099 x P h1)). Qed.
Lemma lem120883 {_9099 : Type'} (P : _9099 -> Prop) (x : _9099) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem120884 {_9099 : Type'} (P : _9099 -> Prop) : (term110 _9099 P) = (term110 _9099 P).
Proof. exact (fun_ext (fun x : _9099 => @lem120883 _9099 P x)). Qed.
Lemma lem120885 {_9099 : Type'} : (@all _9099) = (@all _9099).
Proof. exact (eq_refl (@all _9099)). Qed.
Lemma lem120887 {_9099 : Type'} (P : _9099 -> Prop) : (term95 _9099 P) = (term95 _9099 P).
Proof. exact (MK_COMB (@lem120885 _9099) (@lem120884 _9099 P)). Qed.
Lemma lem120888 {_9099 : Type'} (P : _9099 -> Prop) (x : _9099) (h1 : term145 _9099 P x) : term95 _9099 P.
Proof. exact (EQ_MP (@lem120887 _9099 P) (@lem120879 _9099 P x h1)). Qed.
Lemma lem120898 {_9099 : Type'} (P : _9099 -> Prop) (x : _9099) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem120899 {_9099 : Type'} (P : _9099 -> Prop) : (term110 _9099 P) = (term110 _9099 P).
Proof. exact (fun_ext (fun x : _9099 => @lem120898 _9099 P x)). Qed.
Lemma lem120900 {_9099 : Type'} : (@all _9099) = (@all _9099).
Proof. exact (eq_refl (@all _9099)). Qed.
Lemma lem120902 {_9099 : Type'} (P : _9099 -> Prop) : (term95 _9099 P) = (term95 _9099 P).
Proof. exact (MK_COMB (@lem120900 _9099) (@lem120899 _9099 P)). Qed.
Lemma lem120903 {_9099 : Type'} (x : _9099) (P : _9099 -> Prop) (h1 : term160 _9099 x P) : term95 _9099 P.
Proof. exact (EQ_MP (@lem120902 _9099 P) (@lem120880 _9099 x P h1)). Qed.
Lemma lem120904 {_9099 : Type'} (_2544 : _9099) (P : _9099 -> Prop) (x : _9099) (h1 : term145 _9099 P x) : term115 _9099 P _2544.
Proof. exact (@lem120888 _9099 P x h1 _2544). Qed.
Lemma lem120905 {_9099 : Type'} (P : _9099 -> Prop) (_2544 : _9099) : (term115 _9099 P _2544) = (P _2544).
Proof. exact (eq_refl (term115 _9099 P _2544)). Qed.
Lemma lem120907 {_9099 : Type'} (_2545 : _9099) (x : _9099) (P : _9099 -> Prop) (h1 : term160 _9099 x P) : term115 _9099 P _2545.
Proof. exact (@lem120903 _9099 x P h1 _2545). Qed.
Lemma lem120908 {_9099 : Type'} (P : _9099 -> Prop) (_2545 : _9099) : (term115 _9099 P _2545) = (P _2545).
Proof. exact (eq_refl (term115 _9099 P _2545)). Qed.
Lemma lem120913 {_9099 : Type'} (P : _9099 -> Prop) (x : _9099) (h1 : term145 _9099 P x) : term107 _9099 P x.
Proof. exact (proj2 (@lem120876 _9099 P x h1)). Qed.
Lemma lem120915 {_9099 : Type'} (x : _9099) (P : _9099 -> Prop) (h1 : term160 _9099 x P) : term107 _9099 P x.
Proof. exact (proj1 (@lem120877 _9099 x P h1)). Qed.
Lemma lem120919 {_9099 : Type'} (_2544 : _9099) (P : _9099 -> Prop) (x : _9099) (h1 : term145 _9099 P x) : P _2544.
Proof. exact (EQ_MP (@lem120905 _9099 P _2544) (@lem120904 _9099 _2544 P x h1)). Qed.
Lemma lem120920 {_9099 : Type'} (_2544 : _9099) (P : _9099 -> Prop) (x : _9099) (h1 : term145 _9099 P x) : P _2544.
Proof. exact (@lem120919 _9099 _2544 P x h1). Qed.
Lemma lem120921 {_9099 : Type'} (P : _9099 -> Prop) (x : _9099) (h1 : term145 _9099 P x) : P x.
Proof. exact (@lem120920 _9099 x P x h1). Qed.
Lemma lem120922 {_9099 : Type'} (P : _9099 -> Prop) (x : _9099) (h1 : term145 _9099 P x) : term185 _9099 P x.
Proof. exact (fun h0 : term107 _9099 P x => @lem120921 _9099 P x h1). Qed.
Lemma lem120924 (p : Prop) : (term186 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem120925 {_9099 : Type'} (P : _9099 -> Prop) (x : _9099) : (term185 _9099 P x) = (P x).
Proof. exact (@lem120924 (P x)). Qed.
Lemma lem120926 {_9099 : Type'} (P : _9099 -> Prop) (x : _9099) (h1 : term145 _9099 P x) : P x.
Proof. exact (EQ_MP (@lem120925 _9099 P x) (@lem120922 _9099 P x h1)). Qed.
Lemma lem120929 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem120931 {_9099 : Type'} (P : _9099 -> Prop) (x : _9099) : (term107 _9099 P x) = (term187 _9099 P x).
Proof. exact (@lem120929 (P x)). Qed.
Lemma lem120934 {_9099 : Type'} (P : _9099 -> Prop) (x : _9099) (h1 : term145 _9099 P x) : term187 _9099 P x.
Proof. exact (EQ_MP (@lem120931 _9099 P x) (@lem120913 _9099 P x h1)). Qed.
Lemma lem120937 {_9099 : Type'} (P : _9099 -> Prop) (x : _9099) (h1 : term145 _9099 P x) : False.
Proof. exact (@lem120934 _9099 P x h1 (@lem120926 _9099 P x h1)). Qed.
Lemma lem120938 {_9099 : Type'} (P : _9099 -> Prop) (x : _9099) (h1 : term145 _9099 P x) : term188.
Proof. exact (fun h0 : ~ False => @lem120937 _9099 P x h1). Qed.
Lemma lem120940 (p : Prop) : (term186 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem120941 : term188 = False.
Proof. exact (@lem120940 False). Qed.
Lemma lem120942 {_9099 : Type'} (P : _9099 -> Prop) (x : _9099) (h1 : term145 _9099 P x) : False.
Proof. exact (EQ_MP (@lem120941) (@lem120938 _9099 P x h1)). Qed.
Lemma lem120944 {_9099 : Type'} (_2545 : _9099) (x : _9099) (P : _9099 -> Prop) (h1 : term160 _9099 x P) : P _2545.
Proof. exact (EQ_MP (@lem120908 _9099 P _2545) (@lem120907 _9099 _2545 x P h1)). Qed.
Lemma lem120945 {_9099 : Type'} (_2545 : _9099) (x : _9099) (P : _9099 -> Prop) (h1 : term160 _9099 x P) : P _2545.
Proof. exact (@lem120944 _9099 _2545 x P h1). Qed.
Lemma lem120946 {_9099 : Type'} (x : _9099) (P : _9099 -> Prop) (h1 : term160 _9099 x P) : P x.
Proof. exact (@lem120945 _9099 x x P h1). Qed.
Lemma lem120947 {_9099 : Type'} (x : _9099) (P : _9099 -> Prop) (h1 : term160 _9099 x P) : term185 _9099 P x.
Proof. exact (fun h0 : term107 _9099 P x => @lem120946 _9099 x P h1). Qed.
Lemma lem120949 (p : Prop) : (term186 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem120950 {_9099 : Type'} (P : _9099 -> Prop) (x : _9099) : (term185 _9099 P x) = (P x).
Proof. exact (@lem120949 (P x)). Qed.
Lemma lem120951 {_9099 : Type'} (x : _9099) (P : _9099 -> Prop) (h1 : term160 _9099 x P) : P x.
Proof. exact (EQ_MP (@lem120950 _9099 P x) (@lem120947 _9099 x P h1)). Qed.
Lemma lem120954 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem120956 {_9099 : Type'} (P : _9099 -> Prop) (x : _9099) : (term107 _9099 P x) = (term187 _9099 P x).
Proof. exact (@lem120954 (P x)). Qed.
Lemma lem120959 {_9099 : Type'} (x : _9099) (P : _9099 -> Prop) (h1 : term160 _9099 x P) : term187 _9099 P x.
Proof. exact (EQ_MP (@lem120956 _9099 P x) (@lem120915 _9099 x P h1)). Qed.
Lemma lem120962 {_9099 : Type'} (x : _9099) (P : _9099 -> Prop) (h1 : term160 _9099 x P) : False.
Proof. exact (@lem120959 _9099 x P h1 (@lem120951 _9099 x P h1)). Qed.
Lemma lem120963 {_9099 : Type'} (x : _9099) (P : _9099 -> Prop) (h1 : term160 _9099 x P) : term188.
Proof. exact (fun h0 : ~ False => @lem120962 _9099 x P h1). Qed.
Lemma lem120965 (p : Prop) : (term186 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem120966 : term188 = False.
Proof. exact (@lem120965 False). Qed.
Lemma lem120967 {_9099 : Type'} (x : _9099) (P : _9099 -> Prop) (h1 : term160 _9099 x P) : False.
Proof. exact (EQ_MP (@lem120966) (@lem120963 _9099 x P h1)). Qed.
Lemma lem120968 {_9099 : Type'} (x : _9099) (P : _9099 -> Prop) (h1 : term181 _9099 x P) : False.
Proof. exact (or_elim (@lem120875 _9099 x P h1) (fun h0 : term145 _9099 P x => @lem120942 _9099 P x h0) (fun h0 : term160 _9099 x P => @lem120967 _9099 x P h0)). Qed.
Lemma lem120969 {_9099 : Type'} (x : _9099) (P : _9099 -> Prop) (h1 : term181 _9099 x P) : (term181 _9099 x P) = False.
Proof. exact (prop_ext (fun h2 : term181 _9099 x P => @lem120968 _9099 x P h1) (fun h2 : False => @lem120875 _9099 x P h1)). Qed.
Lemma lem120970 {_9099 : Type'} (x : _9099) (P : _9099 -> Prop) (h1 : term181 _9099 x P) : False.
Proof. exact (EQ_MP (@lem120969 _9099 x P h1) (@lem120875 _9099 x P h1)). Qed.
Lemma lem120971 {_9099 : Type'} (P : _9099 -> Prop) (h1 : term98 _9099 P) : False.
Proof. exact (ex_elim (@lem120842 _9099 P h1) (fun x : _9099 => fun h0 : term183 _9099 P x => @lem120970 _9099 x P h0)). Qed.
Lemma lem120972 {_9099 : Type'} (P : _9099 -> Prop) (h1 : term98 _9099 P) : (term98 _9099 P) = False.
Proof. exact (prop_ext (fun h2 : term98 _9099 P => @lem120971 _9099 P h1) (fun h2 : False => @lem120702 _9099 P h1)). Qed.
Lemma lem120973 {_9099 : Type'} (P : _9099 -> Prop) (h1 : term98 _9099 P) : False.
Proof. exact (EQ_MP (@lem120972 _9099 P h1) (@lem120702 _9099 P h1)). Qed.
Lemma lem120974 {_9099 : Type'} (P : _9099 -> Prop) : term97 _9099 P.
Proof. exact (fun h0 : term98 _9099 P => @lem120973 _9099 P h0). Qed.
Lemma lem120975 {_9099 : Type'} (P : _9099 -> Prop) : (term95 _9099 P) = (term96 _9099 P).
Proof. exact (EQ_MP (@lem120701 _9099 P) (@lem120974 _9099 P)). Qed.
Lemma lem120980 {_9099 : Type'} : term106 _9099.
Proof. exact (fun P : _9099 -> Prop => @lem120975 _9099 P). Qed.
Lemma lem120981 {_9099 : Type'} : term105 _9099.
Proof. exact (EQ_MP (@lem120697 _9099) (@lem120980 _9099)). Qed.
Lemma lem120982 {_9099 : Type'} (P : _9099 -> Prop) : term189 _9099 P.
Proof. exact (@lem120981 _9099 P). Qed.
Lemma lem120983 {_9099 : Type'} (P : _9099 -> Prop) : (term189 _9099 P) = (term97 _9099 P).
Proof. exact (eq_refl (term189 _9099 P)). Qed.
Lemma lem120984 {_9099 : Type'} (P : _9099 -> Prop) : term97 _9099 P.
Proof. exact (EQ_MP (@lem120983 _9099 P) (@lem120982 _9099 P)). Qed.
Lemma lem120986 {_9099 : Type'} (P : _9099 -> Prop) : term97 _9099 P.
Proof. exact (@lem120627 _9099 P (@lem120984 _9099 P)). Qed.
Lemma lem120987 {_9099 : Type'} (P : _9099 -> Prop) (h1 : term98 _9099 P) : False.
Proof. exact (@lem120986 _9099 P (@lem120611 _9099 P h1)). Qed.
Lemma lem120988 {_9099 : Type'} (P : _9099 -> Prop) (h1 : term98 _9099 P) : (term98 _9099 P) = False.
Proof. exact (prop_ext (fun h2 : term98 _9099 P => @lem120987 _9099 P h1) (fun h2 : False => @lem120611 _9099 P h1)). Qed.
Lemma lem120989 {_9099 : Type'} (P : _9099 -> Prop) (h1 : term98 _9099 P) : False.
Proof. exact (EQ_MP (@lem120988 _9099 P h1) (@lem120611 _9099 P h1)). Qed.
Lemma lem120990 {_9099 : Type'} (P : _9099 -> Prop) : term97 _9099 P.
Proof. exact (fun h0 : term98 _9099 P => @lem120989 _9099 P h0). Qed.
Lemma lem120993 (m : nat) (h1 : (S m) = (term190 m)) : (S m) = (term190 m).
Proof. exact (h1). Qed.
Lemma lem120994 (m : nat) (h1 : (S m) = (term190 m)) : (term190 m) = (S m).
Proof. exact (SYM (@lem120993 m h1)). Qed.
Lemma lem120995 (m : nat) (h1 : (term190 m) = (S m)) : (term190 m) = (S m).
Proof. exact (h1). Qed.
Lemma lem120996 (m : nat) (h1 : (term190 m) = (S m)) : (S m) = (term190 m).
Proof. exact (SYM (@lem120995 m h1)). Qed.
Lemma lem120997 (m : nat) : ((S m) = (term190 m)) = ((term190 m) = (S m)).
Proof. exact (prop_ext (fun h1 : (S m) = (term190 m) => @lem120994 m h1) (fun h1 : (term190 m) = (S m) => @lem120996 m h1)). Qed.
Lemma lem120998 : term191 = term192.
Proof. exact (fun_ext (fun m : nat => @lem120997 m)). Qed.
Lemma lem120999 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem121000 : term193 = term194.
Proof. exact (MK_COMB (@lem120999) (@lem120998)). Qed.
Lemma lem121001 : term194.
Proof. exact (EQ_MP (@lem121000) (@lem80621)). Qed.
Lemma lem121002 (m : nat) : term195 m.
Proof. exact (@lem121001 m). Qed.
Lemma lem121003 (m : nat) : (term195 m) = ((term190 m) = (S m)).
Proof. exact (eq_refl (term195 m)). Qed.
Lemma lem121032 (m : nat) : (term190 m) = (S m).
Proof. exact (EQ_MP (@lem121003 m) (@lem121002 m)). Qed.
Lemma lem121033 (n : nat) : (term190 n) = (S n).
Proof. exact (@lem121032 n). Qed.
Lemma lem121034 (P : nat -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem121035 (P : nat -> Prop) (n : nat) : (term196 P n) = (term197 P n).
Proof. exact (MK_COMB (@lem121034 P) (@lem121033 n)). Qed.
Lemma lem121036 (n : nat) (m : nat) : (term198 n m) = (term198 n m).
Proof. exact (eq_refl (term198 n m)). Qed.
Lemma lem121037 (m : nat) (P : nat -> Prop) (n : nat) : (term199 m P n) = (term200 m P n).
Proof. exact (MK_COMB (@lem121036 n m) (@lem121035 P n)). Qed.
Lemma lem121040 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem121041 (m : nat) (P : nat -> Prop) (n : nat) : (term201 m P n) = (term202 m P n).
Proof. exact (MK_COMB (@lem121040) (@lem121037 m P n)). Qed.
Lemma lem121042 (P : nat -> Prop) (n : nat) : (P n) = (P n).
Proof. exact (eq_refl (P n)). Qed.
Lemma lem121043 (m : nat) (P : nat -> Prop) (n : nat) : (term203 m P n) = (term204 m P n).
Proof. exact (MK_COMB (@lem121041 m P n) (@lem121042 P n)). Qed.
Lemma lem121046 (m : nat) (P : nat -> Prop) : (term205 m P) = (term206 m P).
Proof. exact (fun_ext (fun n : nat => @lem121043 m P n)). Qed.
Lemma lem121047 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem121048 (m : nat) (P : nat -> Prop) : (term207 m P) = (term208 m P).
Proof. exact (MK_COMB (@lem121047) (@lem121046 m P)). Qed.
Lemma lem121053 (m : nat) (P : nat -> Prop) : (term209 m P) = (term209 m P).
Proof. exact (eq_refl (term209 m P)). Qed.
Lemma lem121054 (m : nat) (P : nat -> Prop) : (term210 m P) = (term211 m P).
Proof. exact (MK_COMB (@lem121053 m P) (@lem121048 m P)). Qed.
Lemma lem121057 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem121058 (m : nat) (P : nat -> Prop) : (term212 m P) = (term213 m P).
Proof. exact (MK_COMB (@lem121057) (@lem121054 m P)). Qed.
Lemma lem121063 (P : nat -> Prop) : (term214 P) = (term214 P).
Proof. exact (eq_refl (term214 P)). Qed.
Lemma lem121064 (m : nat) (P : nat -> Prop) : (term215 m P) = (term216 m P).
Proof. exact (MK_COMB (@lem121058 m P) (@lem121063 P)). Qed.
Lemma lem121067 (P : nat -> Prop) : (term217 P) = (term218 P).
Proof. exact (fun_ext (fun m : nat => @lem121064 m P)). Qed.
Lemma lem121068 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem121069 (P : nat -> Prop) : (term219 P) = (term220 P).
Proof. exact (MK_COMB (@lem121068) (@lem121067 P)). Qed.
Lemma lem121074 : term221 = term222.
Proof. exact (fun_ext (fun P : nat -> Prop => @lem121069 P)). Qed.
Lemma lem121075 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem121076 : term223 = term224.
Proof. exact (MK_COMB (@lem121075) (@lem121074)). Qed.
Lemma lem121081 : term224 = term223.
Proof. exact (SYM (@lem121076)). Qed.
Lemma lem121082 (m : nat) (P : nat -> Prop) (h1 : term211 m P) : term211 m P.
Proof. exact (h1). Qed.
Lemma lem121083 (m : nat) (P : nat -> Prop) (h1 : term208 m P) : term208 m P.
Proof. exact (h1). Qed.
Lemma lem121084 (m : nat) (P : nat -> Prop) (h1 : term225 m P) : term225 m P.
Proof. exact (h1). Qed.
Lemma lem121090 {_9099 : Type'} (P : _9099 -> Prop) : (term95 _9099 P) = (term96 _9099 P).
Proof. exact (EQ_MP (@lem120610 _9099 P) (@lem120990 _9099 P)). Qed.
Lemma lem121091 (P : nat -> Prop) : (term214 P) = (term226 P).
Proof. exact (@lem121090 nat P). Qed.
Lemma lem121092 (P : nat -> Prop) : (term226 P) = (term214 P).
Proof. exact (SYM (@lem121091 P)). Qed.
Lemma lem121094 (P : nat -> Prop) : (term93 P) = (term94 P).
Proof. exact (EQ_MP (@lem120595 P) (@lem120594 P)). Qed.
Lemma lem121095 (P : nat -> Prop) : (term227 P) = (term228 P).
Proof. exact (@lem121094 (term229 P)). Qed.
Lemma lem121096 (P : nat -> Prop) (n : nat) : (term230 P n) = (term231 P n).
Proof. exact (eq_refl (term230 P n)). Qed.
Lemma lem121097 (P : nat -> Prop) : (term232 P) = (term229 P).
Proof. exact (fun_ext (fun n : nat => @lem121096 P n)). Qed.
Lemma lem121098 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem121099 (P : nat -> Prop) : (term233 P) = (term234 P).
Proof. exact (MK_COMB (@lem121098) (@lem121097 P)). Qed.
Lemma lem121100 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem121101 (P : nat -> Prop) : (term235 P) = (term236 P).
Proof. exact (MK_COMB (@lem121100) (@lem121099 P)). Qed.
Lemma lem121102 (P : nat -> Prop) (n : nat) : (term230 P n) = (term231 P n).
Proof. exact (eq_refl (term230 P n)). Qed.
Lemma lem121103 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem121104 (P : nat -> Prop) (n : nat) : (term237 P n) = (term238 P n).
Proof. exact (MK_COMB (@lem121103) (@lem121102 P n)). Qed.
Lemma lem121105 (n : nat) (M : nat) : (Peano.le n M) = (Peano.le n M).
Proof. exact (eq_refl (Peano.le n M)). Qed.
Lemma lem121106 (P : nat -> Prop) (n : nat) (M : nat) : (term239 P n M) = (term240 P n M).
Proof. exact (MK_COMB (@lem121104 P n) (@lem121105 n M)). Qed.
Lemma lem121107 (P : nat -> Prop) (M : nat) : (term241 P M) = (term242 P M).
Proof. exact (fun_ext (fun n : nat => @lem121106 P n M)). Qed.
Lemma lem121108 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem121109 (P : nat -> Prop) (M : nat) : (term243 P M) = (term244 P M).
Proof. exact (MK_COMB (@lem121108) (@lem121107 P M)). Qed.
Lemma lem121110 (P : nat -> Prop) : (term245 P) = (term246 P).
Proof. exact (fun_ext (fun M : nat => @lem121109 P M)). Qed.
Lemma lem121111 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem121112 (P : nat -> Prop) : (term247 P) = (term248 P).
Proof. exact (MK_COMB (@lem121111) (@lem121110 P)). Qed.
Lemma lem121113 (P : nat -> Prop) : (term227 P) = (term249 P).
Proof. exact (MK_COMB (@lem121101 P) (@lem121112 P)). Qed.
Lemma lem121114 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem121115 (P : nat -> Prop) : (term250 P) = (term251 P).
Proof. exact (MK_COMB (@lem121114) (@lem121113 P)). Qed.
Lemma lem121116 (P : nat -> Prop) (m : nat) : (term230 P m) = (term231 P m).
Proof. exact (eq_refl (term230 P m)). Qed.
Lemma lem121117 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem121118 (P : nat -> Prop) (m : nat) : (term252 P m) = (term253 P m).
Proof. exact (MK_COMB (@lem121117) (@lem121116 P m)). Qed.
Lemma lem121119 (P : nat -> Prop) (n : nat) : (term230 P n) = (term231 P n).
Proof. exact (eq_refl (term230 P n)). Qed.
Lemma lem121120 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem121121 (P : nat -> Prop) (n : nat) : (term237 P n) = (term238 P n).
Proof. exact (MK_COMB (@lem121120) (@lem121119 P n)). Qed.
Lemma lem121122 (n : nat) (m : nat) : (Peano.le n m) = (Peano.le n m).
Proof. exact (eq_refl (Peano.le n m)). Qed.
Lemma lem121123 (P : nat -> Prop) (n : nat) (m : nat) : (term239 P n m) = (term240 P n m).
Proof. exact (MK_COMB (@lem121121 P n) (@lem121122 n m)). Qed.
Lemma lem121124 (P : nat -> Prop) (m : nat) : (term241 P m) = (term242 P m).
Proof. exact (fun_ext (fun n : nat => @lem121123 P n m)). Qed.
Lemma lem121125 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem121126 (P : nat -> Prop) (m : nat) : (term243 P m) = (term244 P m).
Proof. exact (MK_COMB (@lem121125) (@lem121124 P m)). Qed.
Lemma lem121127 (P : nat -> Prop) (m : nat) : (term254 P m) = (term255 P m).
Proof. exact (MK_COMB (@lem121118 P m) (@lem121126 P m)). Qed.
Lemma lem121128 (P : nat -> Prop) : (term256 P) = (term257 P).
Proof. exact (fun_ext (fun m : nat => @lem121127 P m)). Qed.
Lemma lem121129 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem121130 (P : nat -> Prop) : (term228 P) = (term258 P).
Proof. exact (MK_COMB (@lem121129) (@lem121128 P)). Qed.
Lemma lem121131 (P : nat -> Prop) : ((term227 P) = (term228 P)) = ((term249 P) = (term258 P)).
Proof. exact (MK_COMB (@lem121115 P) (@lem121130 P)). Qed.
Lemma lem121132 (P : nat -> Prop) : (term249 P) = (term258 P).
Proof. exact (EQ_MP (@lem121131 P) (@lem121095 P)). Qed.
Lemma lem121134 (q : Prop) (r : Prop) (p : Prop) : term53 q r p.
Proof. exact (@lem120592 q r p (@lem120584 q r p)). Qed.
Lemma lem121135 (P : nat -> Prop) : term259 P.
Proof. exact (@lem121134 (term248 P) (term258 P) (term234 P)). Qed.
Lemma lem121147 (q : Prop) (p : Prop) : (term38 p q) = (term38 q p).
Proof. exact (or_elim (@lem120251 p) (fun h0 : p = True => @lem120346 q p h0) (fun h0 : p = False => @lem120345 q p h0)). Qed.
Lemma lem121148 (M : nat) (P : nat -> Prop) (n : nat) : (term240 P n M) = (term260 M P n).
Proof. exact (@lem121147 (Peano.le n M) (P n)). Qed.
Lemma lem121149 (M : nat) (P : nat -> Prop) : (term242 P M) = (term261 M P).
Proof. exact (fun_ext (fun n : nat => @lem121148 M P n)). Qed.
Lemma lem121150 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem121151 (M : nat) (P : nat -> Prop) : (term244 P M) = (term262 M P).
Proof. exact (MK_COMB (@lem121150) (@lem121149 M P)). Qed.
Lemma lem121152 (P : nat -> Prop) : (term246 P) = (term263 P).
Proof. exact (fun_ext (fun M : nat => @lem121151 M P)). Qed.
Lemma lem121153 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem121154 (P : nat -> Prop) : (term248 P) = (term264 P).
Proof. exact (MK_COMB (@lem121153) (@lem121152 P)). Qed.
Lemma lem121155 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem121156 (P : nat -> Prop) : (term265 P) = (term266 P).
Proof. exact (MK_COMB (@lem121155) (@lem121154 P)). Qed.
Lemma lem121168 (q : Prop) (p : Prop) : (term38 p q) = (term38 q p).
Proof. exact (or_elim (@lem120251 p) (fun h0 : p = True => @lem120346 q p h0) (fun h0 : p = False => @lem120345 q p h0)). Qed.
Lemma lem121169 (m : nat) (P : nat -> Prop) (n : nat) : (term240 P n m) = (term260 m P n).
Proof. exact (@lem121168 (Peano.le n m) (P n)). Qed.
Lemma lem121170 (m : nat) (P : nat -> Prop) : (term242 P m) = (term261 m P).
Proof. exact (fun_ext (fun n : nat => @lem121169 m P n)). Qed.
Lemma lem121171 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem121172 (m : nat) (P : nat -> Prop) : (term244 P m) = (term262 m P).
Proof. exact (MK_COMB (@lem121171) (@lem121170 m P)). Qed.
Lemma lem121173 (P : nat -> Prop) (m : nat) : (term253 P m) = (term253 P m).
Proof. exact (eq_refl (term253 P m)). Qed.
Lemma lem121174 (m : nat) (P : nat -> Prop) : (term255 P m) = (term267 m P).
Proof. exact (MK_COMB (@lem121173 P m) (@lem121172 m P)). Qed.
Lemma lem121175 (P : nat -> Prop) : (term257 P) = (term268 P).
Proof. exact (fun_ext (fun m : nat => @lem121174 m P)). Qed.
Lemma lem121176 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem121177 (P : nat -> Prop) : (term258 P) = (term269 P).
Proof. exact (MK_COMB (@lem121176) (@lem121175 P)). Qed.
Lemma lem121178 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem121179 (P : nat -> Prop) : (term270 P) = (term271 P).
Proof. exact (MK_COMB (@lem121178) (@lem121177 P)). Qed.
Lemma lem121180 (P : nat -> Prop) : (term272 P) = (term273 P).
Proof. exact (MK_COMB (@lem121156 P) (@lem121179 P)). Qed.
Lemma lem121181 (P : nat -> Prop) : (term273 P) = (term272 P).
Proof. exact (SYM (@lem121180 P)). Qed.
Lemma lem121195 (n : nat) (m : nat) : (term28 m n) = (Peano.lt n m).
Proof. exact (EQ_MP (@lem120236 n m) (@lem120235 m n)). Qed.
Lemma lem121196 (M : nat) (n : nat) : (term28 n M) = (Peano.lt M n).
Proof. exact (@lem121195 M n). Qed.
Lemma lem121197 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem121198 (M : nat) (n : nat) : (term274 n M) = (term275 M n).
Proof. exact (MK_COMB (@lem121197) (@lem121196 M n)). Qed.
Lemma lem121199 (P : nat -> Prop) (n : nat) : (P n) = (P n).
Proof. exact (eq_refl (P n)). Qed.
Lemma lem121200 (M : nat) (P : nat -> Prop) (n : nat) : (term260 M P n) = (term276 M P n).
Proof. exact (MK_COMB (@lem121198 M n) (@lem121199 P n)). Qed.
Lemma lem121203 (M : nat) (P : nat -> Prop) : (term261 M P) = (term277 M P).
Proof. exact (fun_ext (fun n : nat => @lem121200 M P n)). Qed.
Lemma lem121204 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem121205 (M : nat) (P : nat -> Prop) : (term262 M P) = (term278 M P).
Proof. exact (MK_COMB (@lem121204) (@lem121203 M P)). Qed.
Lemma lem121210 (P : nat -> Prop) : (term263 P) = (term279 P).
Proof. exact (fun_ext (fun M : nat => @lem121205 M P)). Qed.
Lemma lem121211 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem121212 (P : nat -> Prop) : (term264 P) = (term280 P).
Proof. exact (MK_COMB (@lem121211) (@lem121210 P)). Qed.
Lemma lem121217 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem121218 (P : nat -> Prop) : (term266 P) = (term281 P).
Proof. exact (MK_COMB (@lem121217) (@lem121212 P)). Qed.
Lemma lem121220 {A : Type'} (P : A -> Prop) : (term30 A P) = (term31 A P).
Proof. exact (EQ_MP (@lem120239 A P) (@lem120238 A P)). Qed.
Lemma lem121221 (P : nat -> Prop) : (term282 P) = (term283 P).
Proof. exact (@lem121220 nat P). Qed.
Lemma lem121222 (P : nat -> Prop) : (term284 P) = (term285 P).
Proof. exact (@lem121221 (term268 P)). Qed.
Lemma lem121223 (m : nat) (P : nat -> Prop) : (term286 P m) = (term267 m P).
Proof. exact (eq_refl (term286 P m)). Qed.
Lemma lem121224 (P : nat -> Prop) : (term287 P) = (term268 P).
Proof. exact (fun_ext (fun m : nat => @lem121223 m P)). Qed.
Lemma lem121225 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem121226 (P : nat -> Prop) : (term288 P) = (term269 P).
Proof. exact (MK_COMB (@lem121225) (@lem121224 P)). Qed.
Lemma lem121227 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem121228 (P : nat -> Prop) : (term284 P) = (term271 P).
Proof. exact (MK_COMB (@lem121227) (@lem121226 P)). Qed.
Lemma lem121229 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem121230 (P : nat -> Prop) : (term289 P) = (term290 P).
Proof. exact (MK_COMB (@lem121229) (@lem121228 P)). Qed.
Lemma lem121231 (m : nat) (P : nat -> Prop) : (term286 P m) = (term267 m P).
Proof. exact (eq_refl (term286 P m)). Qed.
Lemma lem121232 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem121233 (m : nat) (P : nat -> Prop) : (term291 P m) = (term292 m P).
Proof. exact (MK_COMB (@lem121232) (@lem121231 m P)). Qed.
Lemma lem121234 (P : nat -> Prop) : (term293 P) = (term294 P).
Proof. exact (fun_ext (fun m : nat => @lem121233 m P)). Qed.
Lemma lem121235 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem121236 (P : nat -> Prop) : (term285 P) = (term295 P).
Proof. exact (MK_COMB (@lem121235) (@lem121234 P)). Qed.
Lemma lem121237 (P : nat -> Prop) : ((term284 P) = (term285 P)) = ((term271 P) = (term295 P)).
Proof. exact (MK_COMB (@lem121230 P) (@lem121236 P)). Qed.
Lemma lem121238 (P : nat -> Prop) : (term271 P) = (term295 P).
Proof. exact (EQ_MP (@lem121237 P) (@lem121222 P)). Qed.
Lemma lem121244 (q : Prop) (p : Prop) : (term14 p q) = (q -> p).
Proof. exact (or_elim (@lem120130 p) (fun h0 : p = True => @lem120228 q p h0) (fun h0 : p = False => @lem120227 q p h0)). Qed.
Lemma lem121245 (P : nat -> Prop) (m : nat) : (term292 m P) = (term296 P m).
Proof. exact (@lem121244 (term262 m P) (P m)). Qed.
Lemma lem121255 (n : nat) (m : nat) : (term28 m n) = (Peano.lt n m).
Proof. exact (EQ_MP (@lem120236 n m) (@lem120235 m n)). Qed.
Lemma lem121256 (m : nat) (n : nat) : (term28 n m) = (Peano.lt m n).
Proof. exact (@lem121255 m n). Qed.
Lemma lem121257 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem121258 (m : nat) (n : nat) : (term274 n m) = (term275 m n).
Proof. exact (MK_COMB (@lem121257) (@lem121256 m n)). Qed.
Lemma lem121259 (P : nat -> Prop) (n : nat) : (P n) = (P n).
Proof. exact (eq_refl (P n)). Qed.
Lemma lem121260 (m : nat) (P : nat -> Prop) (n : nat) : (term260 m P n) = (term276 m P n).
Proof. exact (MK_COMB (@lem121258 m n) (@lem121259 P n)). Qed.
Lemma lem121263 (m : nat) (P : nat -> Prop) : (term261 m P) = (term277 m P).
Proof. exact (fun_ext (fun n : nat => @lem121260 m P n)). Qed.
Lemma lem121264 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem121265 (m : nat) (P : nat -> Prop) : (term262 m P) = (term278 m P).
Proof. exact (MK_COMB (@lem121264) (@lem121263 m P)). Qed.
Lemma lem121270 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem121271 (m : nat) (P : nat -> Prop) : (term297 m P) = (term298 m P).
Proof. exact (MK_COMB (@lem121270) (@lem121265 m P)). Qed.
Lemma lem121272 (P : nat -> Prop) (m : nat) : (P m) = (P m).
Proof. exact (eq_refl (P m)). Qed.
Lemma lem121273 (P : nat -> Prop) (m : nat) : (term296 P m) = (term299 P m).
Proof. exact (MK_COMB (@lem121271 m P) (@lem121272 P m)). Qed.
Lemma lem121276 (P : nat -> Prop) (m : nat) : (term292 m P) = (term299 P m).
Proof. exact (TRANS (@lem121245 P m) (@lem121273 P m)). Qed.
Lemma lem121277 (P : nat -> Prop) : (term294 P) = (term300 P).
Proof. exact (fun_ext (fun m : nat => @lem121276 P m)). Qed.
Lemma lem121278 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem121279 (P : nat -> Prop) : (term295 P) = (term301 P).
Proof. exact (MK_COMB (@lem121278) (@lem121277 P)). Qed.
Lemma lem121284 (P : nat -> Prop) : (term271 P) = (term301 P).
Proof. exact (TRANS (@lem121238 P) (@lem121279 P)). Qed.
Lemma lem121285 (P : nat -> Prop) : (term273 P) = (term302 P).
Proof. exact (MK_COMB (@lem121218 P) (@lem121284 P)). Qed.
Lemma lem121288 (P : nat -> Prop) : (term302 P) = (term273 P).
Proof. exact (SYM (@lem121285 P)). Qed.
Lemma lem121290 (p : Prop) : p = (term42 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem121291 (P : nat -> Prop) : (term302 P) = (term303 P).
Proof. exact (@lem121290 (term302 P)). Qed.
Lemma lem121292 (P : nat -> Prop) : (term303 P) = (term302 P).
Proof. exact (SYM (@lem121291 P)). Qed.
Lemma lem121293 (P : nat -> Prop) (h1 : term304 P) : term304 P.
Proof. exact (h1). Qed.
Lemma lem121296 (m : nat) (P : nat -> Prop) (h1 : term305 m P) : term305 m P.
Proof. exact (h1). Qed.
Lemma lem121297 (m : nat) (P : nat -> Prop) : term306 m P.
Proof. exact (fun h0 : term305 m P => @lem121296 m P h0). Qed.
Lemma lem121298 (m : nat) (P : nat -> Prop) (h1 : term306 m P) : term306 m P.
Proof. exact (h1). Qed.
Lemma lem121299 (m : nat) (P : nat -> Prop) (h1 : term305 m P) : term305 m P.
Proof. exact (h1). Qed.
Lemma lem121300 (m : nat) (P : nat -> Prop) (h1 : term305 m P) (h2 : term306 m P) : term305 m P.
Proof. exact (@lem121298 m P h2 (@lem121299 m P h1)). Qed.
Lemma lem121301 (m : nat) (P : nat -> Prop) (h1 : term305 m P) : term307 m P.
Proof. exact (fun h0 : term306 m P => @lem121300 m P h1 h0). Qed.
Lemma lem121302 (m : nat) (P : nat -> Prop) (h1 : term306 m P) : term306 m P.
Proof. exact (h1). Qed.
Lemma lem121303 (m : nat) (P : nat -> Prop) (h1 : term305 m P) (h2 : term306 m P) : term305 m P.
Proof. exact (@lem121301 m P h1 (@lem121302 m P h2)). Qed.
Lemma lem121304 (m : nat) (P : nat -> Prop) (h1 : term306 m P) : term306 m P.
Proof. exact (fun h0 : term305 m P => @lem121303 m P h0 h1). Qed.
Lemma lem121305 (m : nat) (P : nat -> Prop) : term308 m P.
Proof. exact (fun h0 : term306 m P => @lem121304 m P h0). Qed.
Lemma lem121308 (m : nat) (P : nat -> Prop) : term306 m P.
Proof. exact (@lem121305 m P (@lem121297 m P)). Qed.
Lemma lem121382 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem16464 t)). Qed.
Lemma lem121383 (m : nat) : ((term309 m) = False) = (term310 m).
Proof. exact (@lem121382 (term309 m)). Qed.
Lemma lem121384 : term311 = term312.
Proof. exact (fun_ext (fun m : nat => @lem121383 m)). Qed.
Lemma lem121385 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem121386 : term313 = term314.
Proof. exact (MK_COMB (@lem121385) (@lem121384)). Qed.
Lemma lem121391 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem121392 : term315 = term316.
Proof. exact (MK_COMB (@lem121391) (@lem121386)). Qed.
Lemma lem121403 : term317 = term317.
Proof. exact (eq_refl term317). Qed.
Lemma lem121404 : term318 = term319.
Proof. exact (MK_COMB (@lem121392) (@lem121403)). Qed.
Lemma lem121407 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem121408 : term320 = term321.
Proof. exact (MK_COMB (@lem121407) (@lem121404)). Qed.
Lemma lem121410 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem121411 : term322 = term323.
Proof. exact (@lem121410 term324). Qed.
Lemma lem121466 : term325 = term326.
Proof. exact (MK_COMB (@lem121408) (@lem121411)). Qed.
Lemma lem121469 : term327 = term327.
Proof. exact (eq_refl term327). Qed.
Lemma lem121470 : term328 = term329.
Proof. exact (MK_COMB (@lem121469) (@lem121466)). Qed.
Lemma lem121473 (P : nat -> Prop) : (term330 P) = (term330 P).
Proof. exact (eq_refl (term330 P)). Qed.
Lemma lem121474 (P : nat -> Prop) : (term331 P) = (term332 P).
Proof. exact (MK_COMB (@lem121473 P) (@lem121470)). Qed.
Lemma lem121477 (m : nat) (P : nat -> Prop) : (term333 m P) = (term333 m P).
Proof. exact (eq_refl (term333 m P)). Qed.
Lemma lem121478 (m : nat) (P : nat -> Prop) : (term334 m P) = (term335 m P).
Proof. exact (MK_COMB (@lem121477 m P) (@lem121474 P)). Qed.
Lemma lem121481 (m : nat) (P : nat -> Prop) : (term336 m P) = (term336 m P).
Proof. exact (eq_refl (term336 m P)). Qed.
Lemma lem121482 (m : nat) (P : nat -> Prop) : (term305 m P) = (term337 m P).
Proof. exact (MK_COMB (@lem121481 m P) (@lem121478 m P)). Qed.
Lemma lem121485 (P : nat -> Prop) : (term338 P) = (term339 P).
Proof. exact (fun_ext (fun m : nat => @lem121482 m P)). Qed.
Lemma lem121486 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem121487 (P : nat -> Prop) : (term340 P) = (term341 P).
Proof. exact (MK_COMB (@lem121486) (@lem121485 P)). Qed.
Lemma lem121492 : term342 = term343.
Proof. exact (fun_ext (fun P : nat -> Prop => @lem121487 P)). Qed.
Lemma lem121493 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem121502 : term344 = term345.
Proof. exact (MK_COMB (@lem121493) (@lem121492)). Qed.
Lemma lem121507 (n : nat) (m : nat) : (term346 n m) = (term346 n m).
Proof. exact (eq_refl (term346 n m)). Qed.
Lemma lem121508 (m : nat) : (term347 m) = (term347 m).
Proof. exact (fun_ext (fun n : nat => @lem121507 n m)). Qed.
Lemma lem121509 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem121510 (m : nat) : (term348 m) = (term348 m).
Proof. exact (MK_COMB (@lem121509) (@lem121508 m)). Qed.
Lemma lem121511 : term349 = term349.
Proof. exact (fun_ext (fun m : nat => @lem121510 m)). Qed.
Lemma lem121512 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem121513 : term324 = term324.
Proof. exact (MK_COMB (@lem121512) (@lem121511)). Qed.
Lemma lem121514 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem121515 : term323 = term323.
Proof. exact (MK_COMB (@lem121514) (@lem121513)). Qed.
Lemma lem121524 (m : nat) (n : nat) : ((term350 m n) = (term351 m n)) = ((term350 m n) = (term351 m n)).
Proof. exact (eq_refl ((term350 m n) = (term351 m n))). Qed.
Lemma lem121525 (m : nat) : (term352 m) = (term352 m).
Proof. exact (fun_ext (fun n : nat => @lem121524 m n)). Qed.
Lemma lem121526 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem121527 (m : nat) : (term353 m) = (term353 m).
Proof. exact (MK_COMB (@lem121526) (@lem121525 m)). Qed.
Lemma lem121528 : term354 = term354.
Proof. exact (fun_ext (fun m : nat => @lem121527 m)). Qed.
Lemma lem121529 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem121530 : term317 = term317.
Proof. exact (MK_COMB (@lem121529) (@lem121528)). Qed.
Lemma lem121533 (m : nat) : (term310 m) = (term310 m).
Proof. exact (eq_refl (term310 m)). Qed.
Lemma lem121534 : term312 = term312.
Proof. exact (fun_ext (fun m : nat => @lem121533 m)). Qed.
Lemma lem121535 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem121536 : term314 = term314.
Proof. exact (MK_COMB (@lem121535) (@lem121534)). Qed.
Lemma lem121537 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem121538 : term316 = term316.
Proof. exact (MK_COMB (@lem121537) (@lem121536)). Qed.
Lemma lem121539 : term319 = term319.
Proof. exact (MK_COMB (@lem121538) (@lem121530)). Qed.
Lemma lem121540 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem121541 : term321 = term321.
Proof. exact (MK_COMB (@lem121540) (@lem121539)). Qed.
Lemma lem121542 : term326 = term326.
Proof. exact (MK_COMB (@lem121541) (@lem121515)). Qed.
Lemma lem121547 (m : nat) (n : nat) : (term355 m n) = (term355 m n).
Proof. exact (eq_refl (term355 m n)). Qed.
Lemma lem121548 (m : nat) : (term356 m) = (term356 m).
Proof. exact (fun_ext (fun n : nat => @lem121547 m n)). Qed.
Lemma lem121549 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem121550 (m : nat) : (term357 m) = (term357 m).
Proof. exact (MK_COMB (@lem121549) (@lem121548 m)). Qed.
Lemma lem121551 : term358 = term358.
Proof. exact (fun_ext (fun m : nat => @lem121550 m)). Qed.
Lemma lem121552 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem121553 : term359 = term359.
Proof. exact (MK_COMB (@lem121552) (@lem121551)). Qed.
Lemma lem121554 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem121555 : term327 = term327.
Proof. exact (MK_COMB (@lem121554) (@lem121553)). Qed.
Lemma lem121556 : term329 = term329.
Proof. exact (MK_COMB (@lem121555) (@lem121542)). Qed.
Lemma lem121557 (P : nat -> Prop) (m : nat) : (P m) = (P m).
Proof. exact (eq_refl (P m)). Qed.
Lemma lem121562 (m : nat) (P : nat -> Prop) (n : nat) : (term276 m P n) = (term276 m P n).
Proof. exact (eq_refl (term276 m P n)). Qed.
Lemma lem121563 (m : nat) (P : nat -> Prop) : (term277 m P) = (term277 m P).
Proof. exact (fun_ext (fun n : nat => @lem121562 m P n)). Qed.
Lemma lem121564 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem121565 (m : nat) (P : nat -> Prop) : (term278 m P) = (term278 m P).
Proof. exact (MK_COMB (@lem121564) (@lem121563 m P)). Qed.
Lemma lem121566 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem121567 (m : nat) (P : nat -> Prop) : (term298 m P) = (term298 m P).
Proof. exact (MK_COMB (@lem121566) (@lem121565 m P)). Qed.
Lemma lem121568 (P : nat -> Prop) (m : nat) : (term299 P m) = (term299 P m).
Proof. exact (MK_COMB (@lem121567 m P) (@lem121557 P m)). Qed.
Lemma lem121569 (P : nat -> Prop) : (term300 P) = (term300 P).
Proof. exact (fun_ext (fun m : nat => @lem121568 P m)). Qed.
Lemma lem121570 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem121571 (P : nat -> Prop) : (term301 P) = (term301 P).
Proof. exact (MK_COMB (@lem121570) (@lem121569 P)). Qed.
Lemma lem121576 (M : nat) (P : nat -> Prop) (n : nat) : (term276 M P n) = (term276 M P n).
Proof. exact (eq_refl (term276 M P n)). Qed.
Lemma lem121577 (M : nat) (P : nat -> Prop) : (term277 M P) = (term277 M P).
Proof. exact (fun_ext (fun n : nat => @lem121576 M P n)). Qed.
Lemma lem121578 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem121579 (M : nat) (P : nat -> Prop) : (term278 M P) = (term278 M P).
Proof. exact (MK_COMB (@lem121578) (@lem121577 M P)). Qed.
Lemma lem121580 (P : nat -> Prop) : (term279 P) = (term279 P).
Proof. exact (fun_ext (fun M : nat => @lem121579 M P)). Qed.
Lemma lem121581 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem121582 (P : nat -> Prop) : (term280 P) = (term280 P).
Proof. exact (MK_COMB (@lem121581) (@lem121580 P)). Qed.
Lemma lem121583 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem121584 (P : nat -> Prop) : (term281 P) = (term281 P).
Proof. exact (MK_COMB (@lem121583) (@lem121582 P)). Qed.
Lemma lem121585 (P : nat -> Prop) : (term302 P) = (term302 P).
Proof. exact (MK_COMB (@lem121584 P) (@lem121571 P)). Qed.
Lemma lem121586 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem121587 (P : nat -> Prop) : (term304 P) = (term304 P).
Proof. exact (MK_COMB (@lem121586) (@lem121585 P)). Qed.
Lemma lem121588 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem121589 (P : nat -> Prop) : (term330 P) = (term330 P).
Proof. exact (MK_COMB (@lem121588) (@lem121587 P)). Qed.
Lemma lem121590 (P : nat -> Prop) : (term332 P) = (term332 P).
Proof. exact (MK_COMB (@lem121589 P) (@lem121556)). Qed.
Lemma lem121599 (m : nat) (P : nat -> Prop) (n : nat) : (term204 m P n) = (term204 m P n).
Proof. exact (eq_refl (term204 m P n)). Qed.
Lemma lem121600 (m : nat) (P : nat -> Prop) : (term206 m P) = (term206 m P).
Proof. exact (fun_ext (fun n : nat => @lem121599 m P n)). Qed.
Lemma lem121601 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem121602 (m : nat) (P : nat -> Prop) : (term208 m P) = (term208 m P).
Proof. exact (MK_COMB (@lem121601) (@lem121600 m P)). Qed.
Lemma lem121603 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem121604 (m : nat) (P : nat -> Prop) : (term333 m P) = (term333 m P).
Proof. exact (MK_COMB (@lem121603) (@lem121602 m P)). Qed.
Lemma lem121605 (m : nat) (P : nat -> Prop) : (term335 m P) = (term335 m P).
Proof. exact (MK_COMB (@lem121604 m P) (@lem121590 P)). Qed.
Lemma lem121610 (m : nat) (P : nat -> Prop) (n : nat) : (term360 m P n) = (term360 m P n).
Proof. exact (eq_refl (term360 m P n)). Qed.
Lemma lem121611 (m : nat) (P : nat -> Prop) : (term361 m P) = (term361 m P).
Proof. exact (fun_ext (fun n : nat => @lem121610 m P n)). Qed.
Lemma lem121612 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem121613 (m : nat) (P : nat -> Prop) : (term225 m P) = (term225 m P).
Proof. exact (MK_COMB (@lem121612) (@lem121611 m P)). Qed.
Lemma lem121614 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem121615 (m : nat) (P : nat -> Prop) : (term336 m P) = (term336 m P).
Proof. exact (MK_COMB (@lem121614) (@lem121613 m P)). Qed.
Lemma lem121616 (m : nat) (P : nat -> Prop) : (term337 m P) = (term337 m P).
Proof. exact (MK_COMB (@lem121615 m P) (@lem121605 m P)). Qed.
Lemma lem121617 (P : nat -> Prop) : (term339 P) = (term339 P).
Proof. exact (fun_ext (fun m : nat => @lem121616 m P)). Qed.
Lemma lem121618 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem121619 (P : nat -> Prop) : (term341 P) = (term341 P).
Proof. exact (MK_COMB (@lem121618) (@lem121617 P)). Qed.
Lemma lem121620 : term343 = term343.
Proof. exact (fun_ext (fun P : nat -> Prop => @lem121619 P)). Qed.
Lemma lem121621 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem121622 : term345 = term345.
Proof. exact (MK_COMB (@lem121621) (@lem121620)). Qed.
Lemma lem121747 : term344 = term345.
Proof. exact (TRANS (@lem121502) (@lem121622)). Qed.
Lemma lem121748 : term345 = term344.
Proof. exact (SYM (@lem121747)). Qed.
Lemma lem121749 (m : nat) (P : nat -> Prop) (h1 : term225 m P) : term225 m P.
Proof. exact (h1). Qed.
Lemma lem121750 (m : nat) (P : nat -> Prop) (h1 : term208 m P) : term208 m P.
Proof. exact (h1). Qed.
Lemma lem121751 (P : nat -> Prop) (h1 : term304 P) : term304 P.
Proof. exact (h1). Qed.
Lemma lem121752 (h1 : term359) : term359.
Proof. exact (h1). Qed.
Lemma lem121753 (h1 : term319) : term319.
Proof. exact (h1). Qed.
Lemma lem121754 (h1 : term324) : term324.
Proof. exact (h1). Qed.
Lemma lem121761 (m : nat) (P : nat -> Prop) (n : nat) : (term360 m P n) = (term362 m P n).
Proof. exact (@lem17265 (Peano.le m n) (P n)). Qed.
Lemma lem121762 (m : nat) (P : nat -> Prop) : (term361 m P) = (term363 m P).
Proof. exact (fun_ext (fun n : nat => @lem121761 m P n)). Qed.
Lemma lem121763 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem121800 (m : nat) (P : nat -> Prop) : (term225 m P) = (term364 m P).
Proof. exact (MK_COMB (@lem121763) (@lem121762 m P)). Qed.
Lemma lem121801 (m : nat) (P : nat -> Prop) (h1 : term225 m P) : term364 m P.
Proof. exact (EQ_MP (@lem121800 m P) (@lem121749 m P h1)). Qed.
Lemma lem121808 (m : nat) (P : nat -> Prop) (n : nat) : (term365 m P n) = (term366 m P n).
Proof. exact (@lem17045 (Peano.lt n m) (term197 P n)). Qed.
Lemma lem121809 (P : nat -> Prop) (n : nat) : (P n) = (P n).
Proof. exact (eq_refl (P n)). Qed.
Lemma lem121810 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem121811 (m : nat) (P : nat -> Prop) (n : nat) : (term367 m P n) = (term368 m P n).
Proof. exact (MK_COMB (@lem121810) (@lem121808 m P n)). Qed.
Lemma lem121812 (m : nat) (P : nat -> Prop) (n : nat) : (term369 m P n) = (term370 m P n).
Proof. exact (MK_COMB (@lem121811 m P n) (@lem121809 P n)). Qed.
Lemma lem121813 (m : nat) (P : nat -> Prop) (n : nat) : (term204 m P n) = (term369 m P n).
Proof. exact (@lem17265 (term200 m P n) (P n)). Qed.
Lemma lem121814 (m : nat) (P : nat -> Prop) (n : nat) : (term204 m P n) = (term370 m P n).
Proof. exact (TRANS (@lem121813 m P n) (@lem121812 m P n)). Qed.
Lemma lem121815 (m : nat) (P : nat -> Prop) : (term206 m P) = (term371 m P).
Proof. exact (fun_ext (fun n : nat => @lem121814 m P n)). Qed.
Lemma lem121816 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem121853 (m : nat) (P : nat -> Prop) : (term208 m P) = (term372 m P).
Proof. exact (MK_COMB (@lem121816) (@lem121815 m P)). Qed.
Lemma lem121854 (m : nat) (P : nat -> Prop) (h1 : term208 m P) : term372 m P.
Proof. exact (EQ_MP (@lem121853 m P) (@lem121750 m P h1)). Qed.
Lemma lem121861 (M : nat) (P : nat -> Prop) (n : nat) : (term373 M P n) = (term374 M P n).
Proof. exact (@lem17362 (Peano.lt M n) (P n)). Qed.
Lemma lem121862 (P : nat -> Prop) : (term375 P) = (term234 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem121863 (M : nat) (P : nat -> Prop) : (term376 M P) = (term377 M P).
Proof. exact (@lem121862 (term277 M P)). Qed.
Lemma lem121864 (M : nat) (P : nat -> Prop) (n : nat) : (term378 M P n) = (term276 M P n).
Proof. exact (eq_refl (term378 M P n)). Qed.
Lemma lem121865 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem121866 (M : nat) (P : nat -> Prop) (n : nat) : (term379 M P n) = (term373 M P n).
Proof. exact (MK_COMB (@lem121865) (@lem121864 M P n)). Qed.
Lemma lem121867 (M : nat) (P : nat -> Prop) (n : nat) : (term379 M P n) = (term374 M P n).
Proof. exact (TRANS (@lem121866 M P n) (@lem121861 M P n)). Qed.
Lemma lem121868 (M : nat) (P : nat -> Prop) : (term380 M P) = (term381 M P).
Proof. exact (fun_ext (fun n : nat => @lem121867 M P n)). Qed.
Lemma lem121869 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem121870 (M : nat) (P : nat -> Prop) : (term377 M P) = (term382 M P).
Proof. exact (MK_COMB (@lem121869) (@lem121868 M P)). Qed.
Lemma lem121871 (M : nat) (P : nat -> Prop) : (term376 M P) = (term382 M P).
Proof. exact (TRANS (@lem121863 M P) (@lem121870 M P)). Qed.
Lemma lem121872 (P : nat -> Prop) : (term383 P) = (term283 P).
Proof. exact (@lem18394 nat P). Qed.
Lemma lem121873 (P : nat -> Prop) : (term384 P) = (term385 P).
Proof. exact (@lem121872 (term279 P)). Qed.
Lemma lem121874 (M : nat) (P : nat -> Prop) : (term386 P M) = (term278 M P).
Proof. exact (eq_refl (term386 P M)). Qed.
Lemma lem121875 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem121876 (M : nat) (P : nat -> Prop) : (term387 P M) = (term376 M P).
Proof. exact (MK_COMB (@lem121875) (@lem121874 M P)). Qed.
Lemma lem121877 (M : nat) (P : nat -> Prop) : (term387 P M) = (term382 M P).
Proof. exact (TRANS (@lem121876 M P) (@lem121871 M P)). Qed.
Lemma lem121878 (P : nat -> Prop) : (term388 P) = (term389 P).
Proof. exact (fun_ext (fun M : nat => @lem121877 M P)). Qed.
Lemma lem121879 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem121880 (P : nat -> Prop) : (term385 P) = (term390 P).
Proof. exact (MK_COMB (@lem121879) (@lem121878 P)). Qed.
Lemma lem121881 (P : nat -> Prop) : (term384 P) = (term390 P).
Proof. exact (TRANS (@lem121873 P) (@lem121880 P)). Qed.
Lemma lem121888 (m : nat) (P : nat -> Prop) (n : nat) : (term276 m P n) = (term391 m P n).
Proof. exact (@lem17265 (Peano.lt m n) (P n)). Qed.
Lemma lem121889 (m : nat) (P : nat -> Prop) : (term277 m P) = (term392 m P).
Proof. exact (fun_ext (fun n : nat => @lem121888 m P n)). Qed.
Lemma lem121890 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem121891 (m : nat) (P : nat -> Prop) : (term278 m P) = (term393 m P).
Proof. exact (MK_COMB (@lem121890) (@lem121889 m P)). Qed.
Lemma lem121892 (P : nat -> Prop) (m : nat) : (term231 P m) = (term231 P m).
Proof. exact (eq_refl (term231 P m)). Qed.
Lemma lem121893 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem121894 (m : nat) (P : nat -> Prop) : (term394 m P) = (term395 m P).
Proof. exact (MK_COMB (@lem121893) (@lem121891 m P)). Qed.
Lemma lem121895 (P : nat -> Prop) (m : nat) : (term396 P m) = (term397 P m).
Proof. exact (MK_COMB (@lem121894 m P) (@lem121892 P m)). Qed.
Lemma lem121896 (P : nat -> Prop) (m : nat) : (term398 P m) = (term396 P m).
Proof. exact (@lem17362 (term278 m P) (P m)). Qed.
Lemma lem121897 (P : nat -> Prop) (m : nat) : (term398 P m) = (term397 P m).
Proof. exact (TRANS (@lem121896 P m) (@lem121895 P m)). Qed.
Lemma lem121898 (P : nat -> Prop) : (term375 P) = (term234 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem121899 (P : nat -> Prop) : (term399 P) = (term400 P).
Proof. exact (@lem121898 (term300 P)). Qed.
Lemma lem121900 (P : nat -> Prop) (m : nat) : (term401 P m) = (term299 P m).
Proof. exact (eq_refl (term401 P m)). Qed.
Lemma lem121901 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem121902 (P : nat -> Prop) (m : nat) : (term402 P m) = (term398 P m).
Proof. exact (MK_COMB (@lem121901) (@lem121900 P m)). Qed.
Lemma lem121903 (P : nat -> Prop) (m : nat) : (term402 P m) = (term397 P m).
Proof. exact (TRANS (@lem121902 P m) (@lem121897 P m)). Qed.
Lemma lem121904 (P : nat -> Prop) : (term403 P) = (term404 P).
Proof. exact (fun_ext (fun m : nat => @lem121903 P m)). Qed.
Lemma lem121905 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem121906 (P : nat -> Prop) : (term400 P) = (term405 P).
Proof. exact (MK_COMB (@lem121905) (@lem121904 P)). Qed.
Lemma lem121907 (P : nat -> Prop) : (term399 P) = (term405 P).
Proof. exact (TRANS (@lem121899 P) (@lem121906 P)). Qed.
Lemma lem121908 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem121909 (P : nat -> Prop) : (term406 P) = (term407 P).
Proof. exact (MK_COMB (@lem121908) (@lem121881 P)). Qed.
Lemma lem121910 (P : nat -> Prop) : (term408 P) = (term409 P).
Proof. exact (MK_COMB (@lem121909 P) (@lem121907 P)). Qed.
Lemma lem121911 (P : nat -> Prop) : (term304 P) = (term408 P).
Proof. exact (@lem17045 (term280 P) (term301 P)). Qed.
Lemma lem121912 (P : nat -> Prop) : (term304 P) = (term409 P).
Proof. exact (TRANS (@lem121911 P) (@lem121910 P)). Qed.
Lemma lem122047 {A B : Type'} (P : type1413 A B) : (term410 A B P) = (term411 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem122048 (P : type1605) : (term412 P) = (term413 P).
Proof. exact (@lem122047 nat nat P). Qed.
Lemma lem122049 (P : nat -> Prop) : (term414 P) = (term415 P).
Proof. exact (@lem122048 (term416 P)). Qed.
Lemma lem122050 (M : nat) (P : nat -> Prop) : (term417 P M) = (term381 M P).
Proof. exact (eq_refl (term417 P M)). Qed.
Lemma lem122051 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem122052 (M : nat) (P : nat -> Prop) (n : nat) : (term418 P M n) = (term419 M P n).
Proof. exact (MK_COMB (@lem122050 M P) (@lem122051 n)). Qed.
Lemma lem122053 (M : nat) (P : nat -> Prop) (n : nat) : (term419 M P n) = (term374 M P n).
Proof. exact (eq_refl (term419 M P n)). Qed.
Lemma lem122054 (M : nat) (P : nat -> Prop) (n : nat) : (term418 P M n) = (term374 M P n).
Proof. exact (TRANS (@lem122052 M P n) (@lem122053 M P n)). Qed.
Lemma lem122055 (M : nat) (P : nat -> Prop) : (term420 P M) = (term381 M P).
Proof. exact (fun_ext (fun n : nat => @lem122054 M P n)). Qed.
Lemma lem122056 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem122057 (M : nat) (P : nat -> Prop) : (term421 P M) = (term382 M P).
Proof. exact (MK_COMB (@lem122056) (@lem122055 M P)). Qed.
Lemma lem122058 (P : nat -> Prop) : (term422 P) = (term389 P).
Proof. exact (fun_ext (fun M : nat => @lem122057 M P)). Qed.
Lemma lem122059 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem122060 (P : nat -> Prop) : (term414 P) = (term390 P).
Proof. exact (MK_COMB (@lem122059) (@lem122058 P)). Qed.
Lemma lem122061 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem122062 (P : nat -> Prop) : (term423 P) = (term424 P).
Proof. exact (MK_COMB (@lem122061) (@lem122060 P)). Qed.
Lemma lem122063 (M : nat) (P : nat -> Prop) : (term417 P M) = (term381 M P).
Proof. exact (eq_refl (term417 P M)). Qed.
Lemma lem122064 (n : nat -> nat) (M : nat) : (n M) = (n M).
Proof. exact (eq_refl (n M)). Qed.
Lemma lem122065 (P : nat -> Prop) (n : nat -> nat) (M : nat) : (term425 P n M) = (term426 P n M).
Proof. exact (MK_COMB (@lem122063 M P) (@lem122064 n M)). Qed.
Lemma lem122066 (P : nat -> Prop) (n : nat -> nat) (M : nat) : (term426 P n M) = (term427 P n M).
Proof. exact (eq_refl (term426 P n M)). Qed.
Lemma lem122067 (P : nat -> Prop) (n : nat -> nat) (M : nat) : (term425 P n M) = (term427 P n M).
Proof. exact (TRANS (@lem122065 P n M) (@lem122066 P n M)). Qed.
Lemma lem122068 (P : nat -> Prop) (n : nat -> nat) : (term428 P n) = (term429 P n).
Proof. exact (fun_ext (fun M : nat => @lem122067 P n M)). Qed.
Lemma lem122069 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem122070 (P : nat -> Prop) (n : nat -> nat) : (term430 P n) = (term431 P n).
Proof. exact (MK_COMB (@lem122069) (@lem122068 P n)). Qed.
Lemma lem122071 (P : nat -> Prop) : (term432 P) = (term433 P).
Proof. exact (fun_ext (fun n : nat -> nat => @lem122070 P n)). Qed.
Lemma lem122072 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem122073 (P : nat -> Prop) : (term415 P) = (term434 P).
Proof. exact (MK_COMB (@lem122072) (@lem122071 P)). Qed.
Lemma lem122074 (P : nat -> Prop) : ((term414 P) = (term415 P)) = ((term390 P) = (term434 P)).
Proof. exact (MK_COMB (@lem122062 P) (@lem122073 P)). Qed.
Lemma lem122075 (P : nat -> Prop) : (term390 P) = (term434 P).
Proof. exact (EQ_MP (@lem122074 P) (@lem122049 P)). Qed.
Lemma lem122076 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem122077 (P : nat -> Prop) : (term407 P) = (term435 P).
Proof. exact (MK_COMB (@lem122076) (@lem122075 P)). Qed.
Lemma lem122078 (P : nat -> Prop) : (term405 P) = (term405 P).
Proof. exact (eq_refl (term405 P)). Qed.
Lemma lem122079 (P : nat -> Prop) : (term409 P) = (term436 P).
Proof. exact (MK_COMB (@lem122077 P) (@lem122078 P)). Qed.
Lemma lem122083 {A : Type'} (P : A -> Prop) (Q : Prop) : (term437 A P Q) = (term438 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem122084 (P : type1002) (Q : Prop) : (term439 P Q) = (term440 P Q).
Proof. exact (@lem122083 (nat -> nat) P Q). Qed.
Lemma lem122085 (P : nat -> Prop) : (term441 P) = (term442 P).
Proof. exact (@lem122084 (term433 P) (term405 P)). Qed.
Lemma lem122086 (P : nat -> Prop) (n : nat -> nat) : (term443 P n) = (term431 P n).
Proof. exact (eq_refl (term443 P n)). Qed.
Lemma lem122087 (P : nat -> Prop) : (term444 P) = (term433 P).
Proof. exact (fun_ext (fun n : nat -> nat => @lem122086 P n)). Qed.
Lemma lem122088 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem122089 (P : nat -> Prop) : (term445 P) = (term434 P).
Proof. exact (MK_COMB (@lem122088) (@lem122087 P)). Qed.
Lemma lem122090 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem122091 (P : nat -> Prop) : (term446 P) = (term435 P).
Proof. exact (MK_COMB (@lem122090) (@lem122089 P)). Qed.
Lemma lem122092 (P : nat -> Prop) : (term405 P) = (term405 P).
Proof. exact (eq_refl (term405 P)). Qed.
Lemma lem122093 (P : nat -> Prop) : (term441 P) = (term436 P).
Proof. exact (MK_COMB (@lem122091 P) (@lem122092 P)). Qed.
Lemma lem122094 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem122095 (P : nat -> Prop) : (term447 P) = (term448 P).
Proof. exact (MK_COMB (@lem122094) (@lem122093 P)). Qed.
Lemma lem122096 (P : nat -> Prop) (n : nat -> nat) : (term443 P n) = (term431 P n).
Proof. exact (eq_refl (term443 P n)). Qed.
Lemma lem122097 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem122098 (P : nat -> Prop) (n : nat -> nat) : (term449 P n) = (term450 P n).
Proof. exact (MK_COMB (@lem122097) (@lem122096 P n)). Qed.
Lemma lem122099 (P : nat -> Prop) : (term405 P) = (term405 P).
Proof. exact (eq_refl (term405 P)). Qed.
Lemma lem122100 (n : nat -> nat) (P : nat -> Prop) : (term451 n P) = (term452 n P).
Proof. exact (MK_COMB (@lem122098 P n) (@lem122099 P)). Qed.
Lemma lem122101 (P : nat -> Prop) : (term453 P) = (term454 P).
Proof. exact (fun_ext (fun n : nat -> nat => @lem122100 n P)). Qed.
Lemma lem122102 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem122103 (P : nat -> Prop) : (term442 P) = (term455 P).
Proof. exact (MK_COMB (@lem122102) (@lem122101 P)). Qed.
Lemma lem122104 (P : nat -> Prop) : ((term441 P) = (term442 P)) = ((term436 P) = (term455 P)).
Proof. exact (MK_COMB (@lem122095 P) (@lem122103 P)). Qed.
Lemma lem122105 (P : nat -> Prop) : (term436 P) = (term455 P).
Proof. exact (EQ_MP (@lem122104 P) (@lem122085 P)). Qed.
Lemma lem122107 {A : Type'} (P : Prop) (Q : A -> Prop) : (term456 A P Q) = (term457 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem122108 (P : Prop) (Q : nat -> Prop) : (term458 P Q) = (term459 P Q).
Proof. exact (@lem122107 nat P Q). Qed.
Lemma lem122109 (n : nat -> nat) (P : nat -> Prop) : (term460 n P) = (term461 n P).
Proof. exact (@lem122108 (term431 P n) (term404 P)). Qed.
Lemma lem122110 (P : nat -> Prop) (m : nat) : (term462 P m) = (term397 P m).
Proof. exact (eq_refl (term462 P m)). Qed.
Lemma lem122111 (P : nat -> Prop) : (term463 P) = (term404 P).
Proof. exact (fun_ext (fun m : nat => @lem122110 P m)). Qed.
Lemma lem122112 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem122113 (P : nat -> Prop) : (term464 P) = (term405 P).
Proof. exact (MK_COMB (@lem122112) (@lem122111 P)). Qed.
Lemma lem122114 (P : nat -> Prop) (n : nat -> nat) : (term450 P n) = (term450 P n).
Proof. exact (eq_refl (term450 P n)). Qed.
Lemma lem122115 (n : nat -> nat) (P : nat -> Prop) : (term460 n P) = (term452 n P).
Proof. exact (MK_COMB (@lem122114 P n) (@lem122113 P)). Qed.
Lemma lem122116 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem122117 (n : nat -> nat) (P : nat -> Prop) : (term465 n P) = (term466 n P).
Proof. exact (MK_COMB (@lem122116) (@lem122115 n P)). Qed.
Lemma lem122118 (P : nat -> Prop) (m : nat) : (term462 P m) = (term397 P m).
Proof. exact (eq_refl (term462 P m)). Qed.
Lemma lem122119 (P : nat -> Prop) (n : nat -> nat) : (term450 P n) = (term450 P n).
Proof. exact (eq_refl (term450 P n)). Qed.
Lemma lem122120 (n : nat -> nat) (P : nat -> Prop) (m : nat) : (term467 n P m) = (term468 n P m).
Proof. exact (MK_COMB (@lem122119 P n) (@lem122118 P m)). Qed.
Lemma lem122121 (n : nat -> nat) (P : nat -> Prop) : (term469 n P) = (term470 n P).
Proof. exact (fun_ext (fun m : nat => @lem122120 n P m)). Qed.
Lemma lem122122 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem122123 (n : nat -> nat) (P : nat -> Prop) : (term461 n P) = (term471 n P).
Proof. exact (MK_COMB (@lem122122) (@lem122121 n P)). Qed.
Lemma lem122124 (n : nat -> nat) (P : nat -> Prop) : ((term460 n P) = (term461 n P)) = ((term452 n P) = (term471 n P)).
Proof. exact (MK_COMB (@lem122117 n P) (@lem122123 n P)). Qed.
Lemma lem122125 (n : nat -> nat) (P : nat -> Prop) : (term452 n P) = (term471 n P).
Proof. exact (EQ_MP (@lem122124 n P) (@lem122109 n P)). Qed.
Lemma lem122126 (P : nat -> Prop) : (term454 P) = (term472 P).
Proof. exact (fun_ext (fun n : nat -> nat => @lem122125 n P)). Qed.
Lemma lem122127 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem122128 (P : nat -> Prop) : (term455 P) = (term473 P).
Proof. exact (MK_COMB (@lem122127) (@lem122126 P)). Qed.
Lemma lem122129 (P : nat -> Prop) : (term436 P) = (term473 P).
Proof. exact (TRANS (@lem122105 P) (@lem122128 P)). Qed.
Lemma lem122131 (P : nat -> Prop) : (term409 P) = (term473 P).
Proof. exact (TRANS (@lem122079 P) (@lem122129 P)). Qed.
Lemma lem122132 (P : nat -> Prop) : (term304 P) = (term473 P).
Proof. exact (TRANS (@lem121912 P) (@lem122131 P)). Qed.
Lemma lem122133 (P : nat -> Prop) (h1 : term304 P) : term473 P.
Proof. exact (EQ_MP (@lem122132 P) (@lem121751 P h1)). Qed.
Lemma lem122140 (m : nat) (n : nat) : (term355 m n) = (term474 m n).
Proof. exact (@lem17265 (Peano.lt m n) (Peano.le m n)). Qed.
Lemma lem122141 (m : nat) : (term356 m) = (term475 m).
Proof. exact (fun_ext (fun n : nat => @lem122140 m n)). Qed.
Lemma lem122142 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem122143 (m : nat) : (term357 m) = (term476 m).
Proof. exact (MK_COMB (@lem122142) (@lem122141 m)). Qed.
Lemma lem122144 : term358 = term477.
Proof. exact (fun_ext (fun m : nat => @lem122143 m)). Qed.
Lemma lem122145 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem122202 : term359 = term478.
Proof. exact (MK_COMB (@lem122145) (@lem122144)). Qed.
Lemma lem122203 (h1 : term359) : term478.
Proof. exact (EQ_MP (@lem122202) (@lem121752 h1)). Qed.
Lemma lem122204 (m : nat) : (term310 m) = (term310 m).
Proof. exact (eq_refl (term310 m)). Qed.
Lemma lem122205 : term312 = term312.
Proof. exact (fun_ext (fun m : nat => @lem122204 m)). Qed.
Lemma lem122206 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem122207 : term314 = term314.
Proof. exact (MK_COMB (@lem122206) (@lem122205)). Qed.
Lemma lem122218 (m : nat) (n : nat) : (term479 m n) = (term480 m n).
Proof. exact (@lem17160 (m = n) (Peano.lt m n)). Qed.
Lemma lem122224 (m : nat) (n : nat) : (term481 m n) = (term481 m n).
Proof. exact (eq_refl (term481 m n)). Qed.
Lemma lem122226 (m : nat) (n : nat) : (term482 m n) = (term482 m n).
Proof. exact (eq_refl (term482 m n)). Qed.
Lemma lem122227 (m : nat) (n : nat) : (term483 m n) = (term484 m n).
Proof. exact (MK_COMB (@lem122226 m n) (@lem122218 m n)). Qed.
Lemma lem122228 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem122229 (m : nat) (n : nat) : (term485 m n) = (term486 m n).
Proof. exact (MK_COMB (@lem122228) (@lem122227 m n)). Qed.
Lemma lem122230 (m : nat) (n : nat) : (term487 m n) = (term488 m n).
Proof. exact (MK_COMB (@lem122229 m n) (@lem122224 m n)). Qed.
Lemma lem122231 (m : nat) (n : nat) : ((term350 m n) = (term351 m n)) = (term487 m n).
Proof. exact (@lem17784 (term350 m n) (term351 m n)). Qed.
Lemma lem122232 (m : nat) (n : nat) : ((term350 m n) = (term351 m n)) = (term488 m n).
Proof. exact (TRANS (@lem122231 m n) (@lem122230 m n)). Qed.
Lemma lem122233 (m : nat) : (term352 m) = (term489 m).
Proof. exact (fun_ext (fun n : nat => @lem122232 m n)). Qed.
Lemma lem122234 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem122235 (m : nat) : (term353 m) = (term490 m).
Proof. exact (MK_COMB (@lem122234) (@lem122233 m)). Qed.
Lemma lem122236 : term354 = term491.
Proof. exact (fun_ext (fun m : nat => @lem122235 m)). Qed.
Lemma lem122237 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem122238 : term317 = term492.
Proof. exact (MK_COMB (@lem122237) (@lem122236)). Qed.
Lemma lem122239 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem122240 : term316 = term316.
Proof. exact (MK_COMB (@lem122239) (@lem122207)). Qed.
Lemma lem122241 : term319 = term493.
Proof. exact (MK_COMB (@lem122240) (@lem122238)). Qed.
Lemma lem122251 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term494 A P Q) = (term495 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem122252 (P : nat -> Prop) (Q : nat -> Prop) : (term496 P Q) = (term497 P Q).
Proof. exact (@lem122251 nat P Q). Qed.
Lemma lem122253 (m : nat) : (term498 m) = (term499 m).
Proof. exact (@lem122252 (term500 m) (term501 m)). Qed.
Lemma lem122254 (m : nat) (n : nat) : (term502 m n) = (term484 m n).
Proof. exact (eq_refl (term502 m n)). Qed.
Lemma lem122255 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem122256 (m : nat) (n : nat) : (term503 m n) = (term486 m n).
Proof. exact (MK_COMB (@lem122255) (@lem122254 m n)). Qed.
Lemma lem122257 (m : nat) (n : nat) : (term504 m n) = (term481 m n).
Proof. exact (eq_refl (term504 m n)). Qed.
Lemma lem122258 (m : nat) (n : nat) : (term505 m n) = (term488 m n).
Proof. exact (MK_COMB (@lem122256 m n) (@lem122257 m n)). Qed.
Lemma lem122259 (m : nat) : (term506 m) = (term489 m).
Proof. exact (fun_ext (fun n : nat => @lem122258 m n)). Qed.
Lemma lem122260 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem122261 (m : nat) : (term498 m) = (term490 m).
Proof. exact (MK_COMB (@lem122260) (@lem122259 m)). Qed.
Lemma lem122262 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem122263 (m : nat) : (term507 m) = (term508 m).
Proof. exact (MK_COMB (@lem122262) (@lem122261 m)). Qed.
Lemma lem122264 (m : nat) (n : nat) : (term502 m n) = (term484 m n).
Proof. exact (eq_refl (term502 m n)). Qed.
Lemma lem122265 (m : nat) : (term509 m) = (term500 m).
Proof. exact (fun_ext (fun n : nat => @lem122264 m n)). Qed.
Lemma lem122266 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem122267 (m : nat) : (term510 m) = (term511 m).
Proof. exact (MK_COMB (@lem122266) (@lem122265 m)). Qed.
Lemma lem122268 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem122269 (m : nat) : (term512 m) = (term513 m).
Proof. exact (MK_COMB (@lem122268) (@lem122267 m)). Qed.
Lemma lem122270 (m : nat) (n : nat) : (term504 m n) = (term481 m n).
Proof. exact (eq_refl (term504 m n)). Qed.
Lemma lem122271 (m : nat) : (term514 m) = (term501 m).
Proof. exact (fun_ext (fun n : nat => @lem122270 m n)). Qed.
Lemma lem122272 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem122273 (m : nat) : (term515 m) = (term516 m).
Proof. exact (MK_COMB (@lem122272) (@lem122271 m)). Qed.
Lemma lem122274 (m : nat) : (term499 m) = (term517 m).
Proof. exact (MK_COMB (@lem122269 m) (@lem122273 m)). Qed.
Lemma lem122275 (m : nat) : ((term498 m) = (term499 m)) = ((term490 m) = (term517 m)).
Proof. exact (MK_COMB (@lem122263 m) (@lem122274 m)). Qed.
Lemma lem122276 (m : nat) : (term490 m) = (term517 m).
Proof. exact (EQ_MP (@lem122275 m) (@lem122253 m)). Qed.
Lemma lem122373 : term491 = term518.
Proof. exact (fun_ext (fun m : nat => @lem122276 m)). Qed.
Lemma lem122374 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem122375 : term492 = term519.
Proof. exact (MK_COMB (@lem122374) (@lem122373)). Qed.
Lemma lem122377 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term494 A P Q) = (term495 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem122378 (P : nat -> Prop) (Q : nat -> Prop) : (term496 P Q) = (term497 P Q).
Proof. exact (@lem122377 nat P Q). Qed.
Lemma lem122379 : term520 = term521.
Proof. exact (@lem122378 term522 term523). Qed.
Lemma lem122380 (m : nat) : (term524 m) = (term511 m).
Proof. exact (eq_refl (term524 m)). Qed.
Lemma lem122381 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem122382 (m : nat) : (term525 m) = (term513 m).
Proof. exact (MK_COMB (@lem122381) (@lem122380 m)). Qed.
Lemma lem122383 (m : nat) : (term526 m) = (term516 m).
Proof. exact (eq_refl (term526 m)). Qed.
Lemma lem122384 (m : nat) : (term527 m) = (term517 m).
Proof. exact (MK_COMB (@lem122382 m) (@lem122383 m)). Qed.
Lemma lem122385 : term528 = term518.
Proof. exact (fun_ext (fun m : nat => @lem122384 m)). Qed.
Lemma lem122386 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem122387 : term520 = term519.
Proof. exact (MK_COMB (@lem122386) (@lem122385)). Qed.
Lemma lem122388 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem122389 : term529 = term530.
Proof. exact (MK_COMB (@lem122388) (@lem122387)). Qed.
Lemma lem122390 (m : nat) : (term524 m) = (term511 m).
Proof. exact (eq_refl (term524 m)). Qed.
Lemma lem122391 : term531 = term522.
Proof. exact (fun_ext (fun m : nat => @lem122390 m)). Qed.
Lemma lem122392 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem122393 : term532 = term533.
Proof. exact (MK_COMB (@lem122392) (@lem122391)). Qed.
Lemma lem122394 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem122395 : term534 = term535.
Proof. exact (MK_COMB (@lem122394) (@lem122393)). Qed.
Lemma lem122396 (m : nat) : (term526 m) = (term516 m).
Proof. exact (eq_refl (term526 m)). Qed.
Lemma lem122397 : term536 = term523.
Proof. exact (fun_ext (fun m : nat => @lem122396 m)). Qed.
Lemma lem122398 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem122399 : term537 = term538.
Proof. exact (MK_COMB (@lem122398) (@lem122397)). Qed.
Lemma lem122400 : term521 = term539.
Proof. exact (MK_COMB (@lem122395) (@lem122399)). Qed.
Lemma lem122401 : (term520 = term521) = (term519 = term539).
Proof. exact (MK_COMB (@lem122389) (@lem122400)). Qed.
Lemma lem122402 : term519 = term539.
Proof. exact (EQ_MP (@lem122401) (@lem122379)). Qed.
Lemma lem122507 : term492 = term539.
Proof. exact (TRANS (@lem122375) (@lem122402)). Qed.
Lemma lem122508 : term316 = term316.
Proof. exact (eq_refl term316). Qed.
Lemma lem122511 : term493 = term540.
Proof. exact (MK_COMB (@lem122508) (@lem122507)). Qed.
Lemma lem122512 : term319 = term540.
Proof. exact (TRANS (@lem122241) (@lem122511)). Qed.
Lemma lem122513 (h1 : term319) : term540.
Proof. exact (EQ_MP (@lem122512) (@lem121753 h1)). Qed.
Lemma lem122518 (n : nat) (m : nat) : (term346 n m) = (term346 n m).
Proof. exact (eq_refl (term346 n m)). Qed.
Lemma lem122519 (m : nat) : (term347 m) = (term347 m).
Proof. exact (fun_ext (fun n : nat => @lem122518 n m)). Qed.
Lemma lem122520 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem122521 (m : nat) : (term348 m) = (term348 m).
Proof. exact (MK_COMB (@lem122520) (@lem122519 m)). Qed.
Lemma lem122522 : term349 = term349.
Proof. exact (fun_ext (fun m : nat => @lem122521 m)). Qed.
Lemma lem122523 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem122580 : term324 = term324.
Proof. exact (MK_COMB (@lem122523) (@lem122522)). Qed.
Lemma lem122581 (h1 : term324) : term324.
Proof. exact (EQ_MP (@lem122580) (@lem121754 h1)). Qed.
Lemma lem122582 (n : nat -> nat) (P : nat -> Prop) (h1 : term471 n P) : term471 n P.
Proof. exact (h1). Qed.
Lemma lem122583 (n : nat -> nat) (P : nat -> Prop) (m' : nat) (h1 : term468 n P m') : term468 n P m'.
Proof. exact (h1). Qed.
Lemma lem122596 (m : nat) (P : nat -> Prop) (n : nat) : (term362 m P n) = (term362 m P n).
Proof. exact (eq_refl (term362 m P n)). Qed.
Lemma lem122597 (m : nat) (P : nat -> Prop) : (term363 m P) = (term363 m P).
Proof. exact (fun_ext (fun n : nat => @lem122596 m P n)). Qed.
Lemma lem122598 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem122599 (m : nat) (P : nat -> Prop) : (term364 m P) = (term364 m P).
Proof. exact (MK_COMB (@lem122598) (@lem122597 m P)). Qed.
Lemma lem122600 (m : nat) (P : nat -> Prop) (h1 : term225 m P) : term364 m P.
Proof. exact (EQ_MP (@lem122599 m P) (@lem121801 m P h1)). Qed.
Lemma lem122623 (m : nat) (P : nat -> Prop) (n : nat) : (term370 m P n) = (term370 m P n).
Proof. exact (eq_refl (term370 m P n)). Qed.
Lemma lem122624 (m : nat) (P : nat -> Prop) : (term371 m P) = (term371 m P).
Proof. exact (fun_ext (fun n : nat => @lem122623 m P n)). Qed.
Lemma lem122625 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem122626 (m : nat) (P : nat -> Prop) : (term372 m P) = (term372 m P).
Proof. exact (MK_COMB (@lem122625) (@lem122624 m P)). Qed.
Lemma lem122627 (m : nat) (P : nat -> Prop) (h1 : term208 m P) : term372 m P.
Proof. exact (EQ_MP (@lem122626 m P) (@lem121854 m P h1)). Qed.
Lemma lem122642 (m : nat) (n : nat) : (term474 m n) = (term474 m n).
Proof. exact (eq_refl (term474 m n)). Qed.
Lemma lem122643 (m : nat) : (term475 m) = (term475 m).
Proof. exact (fun_ext (fun n : nat => @lem122642 m n)). Qed.
Lemma lem122644 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem122645 (m : nat) : (term476 m) = (term476 m).
Proof. exact (MK_COMB (@lem122644) (@lem122643 m)). Qed.
Lemma lem122646 : term477 = term477.
Proof. exact (fun_ext (fun m : nat => @lem122645 m)). Qed.
Lemma lem122647 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem122648 : term478 = term478.
Proof. exact (MK_COMB (@lem122647) (@lem122646)). Qed.
Lemma lem122649 (h1 : term359) : term478.
Proof. exact (EQ_MP (@lem122648) (@lem122203 h1)). Qed.
Lemma lem122674 (m : nat) (n : nat) : (term481 m n) = (term481 m n).
Proof. exact (eq_refl (term481 m n)). Qed.
Lemma lem122675 (m : nat) : (term501 m) = (term501 m).
Proof. exact (fun_ext (fun n : nat => @lem122674 m n)). Qed.
Lemma lem122676 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem122677 (m : nat) : (term516 m) = (term516 m).
Proof. exact (MK_COMB (@lem122676) (@lem122675 m)). Qed.
Lemma lem122678 : term523 = term523.
Proof. exact (fun_ext (fun m : nat => @lem122677 m)). Qed.
Lemma lem122679 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem122680 : term538 = term538.
Proof. exact (MK_COMB (@lem122679) (@lem122678)). Qed.
Lemma lem122707 (m : nat) (n : nat) : (term484 m n) = (term484 m n).
Proof. exact (eq_refl (term484 m n)). Qed.
Lemma lem122708 (m : nat) : (term500 m) = (term500 m).
Proof. exact (fun_ext (fun n : nat => @lem122707 m n)). Qed.
Lemma lem122709 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem122710 (m : nat) : (term511 m) = (term511 m).
Proof. exact (MK_COMB (@lem122709) (@lem122708 m)). Qed.
Lemma lem122711 : term522 = term522.
Proof. exact (fun_ext (fun m : nat => @lem122710 m)). Qed.
Lemma lem122712 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem122713 : term533 = term533.
Proof. exact (MK_COMB (@lem122712) (@lem122711)). Qed.
Lemma lem122714 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem122715 : term535 = term535.
Proof. exact (MK_COMB (@lem122714) (@lem122713)). Qed.
Lemma lem122716 : term539 = term539.
Proof. exact (MK_COMB (@lem122715) (@lem122680)). Qed.
Lemma lem122725 (m : nat) : (term310 m) = (term310 m).
Proof. exact (eq_refl (term310 m)). Qed.
Lemma lem122726 : term312 = term312.
Proof. exact (fun_ext (fun m : nat => @lem122725 m)). Qed.
Lemma lem122727 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem122728 : term314 = term314.
Proof. exact (MK_COMB (@lem122727) (@lem122726)). Qed.
Lemma lem122729 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem122730 : term316 = term316.
Proof. exact (MK_COMB (@lem122729) (@lem122728)). Qed.
Lemma lem122731 : term540 = term540.
Proof. exact (MK_COMB (@lem122730) (@lem122716)). Qed.
Lemma lem122732 (h1 : term319) : term540.
Proof. exact (EQ_MP (@lem122731) (@lem122513 h1)). Qed.
Lemma lem122745 (n : nat) (m : nat) : (term346 n m) = (term346 n m).
Proof. exact (eq_refl (term346 n m)). Qed.
Lemma lem122746 (m : nat) : (term347 m) = (term347 m).
Proof. exact (fun_ext (fun n : nat => @lem122745 n m)). Qed.
Lemma lem122747 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem122748 (m : nat) : (term348 m) = (term348 m).
Proof. exact (MK_COMB (@lem122747) (@lem122746 m)). Qed.
Lemma lem122749 : term349 = term349.
Proof. exact (fun_ext (fun m : nat => @lem122748 m)). Qed.
Lemma lem122750 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem122751 : term324 = term324.
Proof. exact (MK_COMB (@lem122750) (@lem122749)). Qed.
Lemma lem122752 (h1 : term324) : term324.
Proof. exact (EQ_MP (@lem122751) (@lem122581 h1)). Qed.
Lemma lem122757 (P : nat -> Prop) (m' : nat) : (term231 P m') = (term231 P m').
Proof. exact (eq_refl (term231 P m')). Qed.
Lemma lem122770 (m' : nat) (P : nat -> Prop) (n : nat) : (term391 m' P n) = (term391 m' P n).
Proof. exact (eq_refl (term391 m' P n)). Qed.
Lemma lem122771 (m' : nat) (P : nat -> Prop) : (term392 m' P) = (term392 m' P).
Proof. exact (fun_ext (fun n : nat => @lem122770 m' P n)). Qed.
Lemma lem122772 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem122773 (m' : nat) (P : nat -> Prop) : (term393 m' P) = (term393 m' P).
Proof. exact (MK_COMB (@lem122772) (@lem122771 m' P)). Qed.
Lemma lem122774 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem122775 (m' : nat) (P : nat -> Prop) : (term395 m' P) = (term395 m' P).
Proof. exact (MK_COMB (@lem122774) (@lem122773 m' P)). Qed.
Lemma lem122776 (P : nat -> Prop) (m' : nat) : (term397 P m') = (term397 P m').
Proof. exact (MK_COMB (@lem122775 m' P) (@lem122757 P m')). Qed.
Lemma lem122793 (P : nat -> Prop) (n : nat -> nat) (M : nat) : (term427 P n M) = (term427 P n M).
Proof. exact (eq_refl (term427 P n M)). Qed.
Lemma lem122794 (P : nat -> Prop) (n : nat -> nat) : (term429 P n) = (term429 P n).
Proof. exact (fun_ext (fun M : nat => @lem122793 P n M)). Qed.
Lemma lem122795 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem122796 (P : nat -> Prop) (n : nat -> nat) : (term431 P n) = (term431 P n).
Proof. exact (MK_COMB (@lem122795) (@lem122794 P n)). Qed.
Lemma lem122797 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem122798 (P : nat -> Prop) (n : nat -> nat) : (term450 P n) = (term450 P n).
Proof. exact (MK_COMB (@lem122797) (@lem122796 P n)). Qed.
Lemma lem122799 (n : nat -> nat) (P : nat -> Prop) (m' : nat) : (term468 n P m') = (term468 n P m').
Proof. exact (MK_COMB (@lem122798 P n) (@lem122776 P m')). Qed.
Lemma lem122800 (n : nat -> nat) (P : nat -> Prop) (m' : nat) (h1 : term468 n P m') : term468 n P m'.
Proof. exact (EQ_MP (@lem122799 n P m') (@lem122583 n P m' h1)). Qed.
Lemma lem122801 (h1 : term319) : term539.
Proof. exact (proj2 (@lem122732 h1)). Qed.
Lemma lem122804 (h1 : term319) : term533.
Proof. exact (proj1 (@lem122801 h1)). Qed.
Lemma lem122805 (P : nat -> Prop) (n : nat -> nat) (h1 : term431 P n) : term431 P n.
Proof. exact (h1). Qed.
Lemma lem122806 (P : nat -> Prop) (m' : nat) (h1 : term397 P m') : term397 P m'.
Proof. exact (h1). Qed.
Lemma lem122808 (P : nat -> Prop) (m' : nat) (h1 : term397 P m') : term393 m' P.
Proof. exact (proj1 (@lem122806 P m' h1)). Qed.
Lemma lem122816 (m : nat) (P : nat -> Prop) (n : nat) : (term362 m P n) = (term362 m P n).
Proof. exact (eq_refl (term362 m P n)). Qed.
Lemma lem122817 (m : nat) (P : nat -> Prop) : (term363 m P) = (term363 m P).
Proof. exact (fun_ext (fun n : nat => @lem122816 m P n)). Qed.
Lemma lem122818 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem122820 (m : nat) (P : nat -> Prop) : (term364 m P) = (term364 m P).
Proof. exact (MK_COMB (@lem122818) (@lem122817 m P)). Qed.
Lemma lem122821 (m : nat) (P : nat -> Prop) (h1 : term225 m P) : term364 m P.
Proof. exact (EQ_MP (@lem122820 m P) (@lem122600 m P h1)). Qed.
Lemma lem122848 (m : nat) (n : nat) : (term474 m n) = (term474 m n).
Proof. exact (eq_refl (term474 m n)). Qed.
Lemma lem122849 (m : nat) : (term475 m) = (term475 m).
Proof. exact (fun_ext (fun n : nat => @lem122848 m n)). Qed.
Lemma lem122850 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem122851 (m : nat) : (term476 m) = (term476 m).
Proof. exact (MK_COMB (@lem122850) (@lem122849 m)). Qed.
Lemma lem122852 : term477 = term477.
Proof. exact (fun_ext (fun m : nat => @lem122851 m)). Qed.
Lemma lem122853 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem122855 : term478 = term478.
Proof. exact (MK_COMB (@lem122853) (@lem122852)). Qed.
Lemma lem122856 (h1 : term359) : term478.
Proof. exact (EQ_MP (@lem122855) (@lem122649 h1)). Qed.
Lemma lem122933 (P : nat -> Prop) (n : nat -> nat) (M : nat) : (term427 P n M) = (term427 P n M).
Proof. exact (eq_refl (term427 P n M)). Qed.
Lemma lem122934 (P : nat -> Prop) (n : nat -> nat) : (term429 P n) = (term429 P n).
Proof. exact (fun_ext (fun M : nat => @lem122933 P n M)). Qed.
Lemma lem122935 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem122937 (P : nat -> Prop) (n : nat -> nat) : (term431 P n) = (term431 P n).
Proof. exact (MK_COMB (@lem122935) (@lem122934 P n)). Qed.
Lemma lem122938 (P : nat -> Prop) (n : nat -> nat) (h1 : term431 P n) : term431 P n.
Proof. exact (EQ_MP (@lem122937 P n) (@lem122805 P n h1)). Qed.
Lemma lem122946 (m : nat) (P : nat -> Prop) (n : nat) : (term362 m P n) = (term362 m P n).
Proof. exact (eq_refl (term362 m P n)). Qed.
Lemma lem122947 (m : nat) (P : nat -> Prop) : (term363 m P) = (term363 m P).
Proof. exact (fun_ext (fun n : nat => @lem122946 m P n)). Qed.
Lemma lem122948 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem122950 (m : nat) (P : nat -> Prop) : (term364 m P) = (term364 m P).
Proof. exact (MK_COMB (@lem122948) (@lem122947 m P)). Qed.
Lemma lem122951 (m : nat) (P : nat -> Prop) (h1 : term225 m P) : term364 m P.
Proof. exact (EQ_MP (@lem122950 m P) (@lem122600 m P h1)). Qed.
Lemma lem122965 (m : nat) (P : nat -> Prop) (n : nat) : (term370 m P n) = (term370 m P n).
Proof. exact (eq_refl (term370 m P n)). Qed.
Lemma lem122966 (m : nat) (P : nat -> Prop) : (term371 m P) = (term371 m P).
Proof. exact (fun_ext (fun n : nat => @lem122965 m P n)). Qed.
Lemma lem122967 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem122969 (m : nat) (P : nat -> Prop) : (term372 m P) = (term372 m P).
Proof. exact (MK_COMB (@lem122967) (@lem122966 m P)). Qed.
Lemma lem122970 (m : nat) (P : nat -> Prop) (h1 : term208 m P) : term372 m P.
Proof. exact (EQ_MP (@lem122969 m P) (@lem122627 m P h1)). Qed.
Lemma lem122994 (n : nat) (m : nat) : (term346 n m) = (term346 n m).
Proof. exact (eq_refl (term346 n m)). Qed.
Lemma lem122995 (m : nat) : (term347 m) = (term347 m).
Proof. exact (fun_ext (fun n : nat => @lem122994 n m)). Qed.
Lemma lem122996 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem122997 (m : nat) : (term348 m) = (term348 m).
Proof. exact (MK_COMB (@lem122996) (@lem122995 m)). Qed.
Lemma lem122998 : term349 = term349.
Proof. exact (fun_ext (fun m : nat => @lem122997 m)). Qed.
Lemma lem122999 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem123001 : term324 = term324.
Proof. exact (MK_COMB (@lem122999) (@lem122998)). Qed.
Lemma lem123002 (h1 : term324) : term324.
Proof. exact (EQ_MP (@lem123001) (@lem122752 h1)). Qed.
Lemma lem123027 (m : nat) (n : nat) : (term484 m n) = (term541 m n).
Proof. exact (@lem19490 (term542 m n) (term350 m n) (term543 m n)). Qed.
Lemma lem123028 (m : nat) : (term500 m) = (term544 m).
Proof. exact (fun_ext (fun n : nat => @lem123027 m n)). Qed.
Lemma lem123029 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem123030 (m : nat) : (term511 m) = (term545 m).
Proof. exact (MK_COMB (@lem123029) (@lem123028 m)). Qed.
Lemma lem123031 : term522 = term546.
Proof. exact (fun_ext (fun m : nat => @lem123030 m)). Qed.
Lemma lem123032 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem123034 : term533 = term547.
Proof. exact (MK_COMB (@lem123032) (@lem123031)). Qed.
Lemma lem123035 (h1 : term319) : term547.
Proof. exact (EQ_MP (@lem123034) (@lem122804 h1)). Qed.
Lemma lem123065 (m' : nat) (P : nat -> Prop) (n : nat) : (term391 m' P n) = (term391 m' P n).
Proof. exact (eq_refl (term391 m' P n)). Qed.
Lemma lem123066 (m' : nat) (P : nat -> Prop) : (term392 m' P) = (term392 m' P).
Proof. exact (fun_ext (fun n : nat => @lem123065 m' P n)). Qed.
Lemma lem123067 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem123069 (m' : nat) (P : nat -> Prop) : (term393 m' P) = (term393 m' P).
Proof. exact (MK_COMB (@lem123067) (@lem123066 m' P)). Qed.
Lemma lem123070 (P : nat -> Prop) (m' : nat) (h1 : term397 P m') : term393 m' P.
Proof. exact (EQ_MP (@lem123069 m' P) (@lem122808 P m' h1)). Qed.
Lemma lem123075 (_2546 : nat) (m : nat) (P : nat -> Prop) (h1 : term225 m P) : term548 m P _2546.
Proof. exact (@lem122821 m P h1 _2546). Qed.
Lemma lem123076 (m : nat) (P : nat -> Prop) (_2546 : nat) : (term548 m P _2546) = (term362 m P _2546).
Proof. exact (eq_refl (term548 m P _2546)). Qed.
Lemma lem123081 (_2548 : nat) (h1 : term359) : term549 _2548.
Proof. exact (@lem122856 h1 _2548). Qed.
Lemma lem123082 (_2548 : nat) : (term549 _2548) = (term476 _2548).
Proof. exact (eq_refl (term549 _2548)). Qed.
Lemma lem123083 (_2548 : nat) (h1 : term359) : term476 _2548.
Proof. exact (EQ_MP (@lem123082 _2548) (@lem123081 _2548 h1)). Qed.
Lemma lem123084 (_2548 : nat) (_2549 : nat) (h1 : term359) : term550 _2548 _2549.
Proof. exact (@lem123083 _2548 h1 _2549). Qed.
Lemma lem123085 (_2548 : nat) (_2549 : nat) : (term550 _2548 _2549) = (term474 _2548 _2549).
Proof. exact (eq_refl (term550 _2548 _2549)). Qed.
Lemma lem123108 (_2557 : nat) (P : nat -> Prop) (n : nat -> nat) (h1 : term431 P n) : term551 P n _2557.
Proof. exact (@lem122938 P n h1 _2557). Qed.
Lemma lem123109 (P : nat -> Prop) (n : nat -> nat) (_2557 : nat) : (term551 P n _2557) = (term427 P n _2557).
Proof. exact (eq_refl (term551 P n _2557)). Qed.
Lemma lem123110 (_2557 : nat) (P : nat -> Prop) (n : nat -> nat) (h1 : term431 P n) : term427 P n _2557.
Proof. exact (EQ_MP (@lem123109 P n _2557) (@lem123108 _2557 P n h1)). Qed.
Lemma lem123111 (_2558 : nat) (m : nat) (P : nat -> Prop) (h1 : term225 m P) : term548 m P _2558.
Proof. exact (@lem122951 m P h1 _2558). Qed.
Lemma lem123112 (m : nat) (P : nat -> Prop) (_2558 : nat) : (term548 m P _2558) = (term362 m P _2558).
Proof. exact (eq_refl (term548 m P _2558)). Qed.
Lemma lem123114 (_2559 : nat) (m : nat) (P : nat -> Prop) (h1 : term208 m P) : term552 m P _2559.
Proof. exact (@lem122970 m P h1 _2559). Qed.
Lemma lem123115 (m : nat) (P : nat -> Prop) (_2559 : nat) : (term552 m P _2559) = (term370 m P _2559).
Proof. exact (eq_refl (term552 m P _2559)). Qed.
Lemma lem123116 (_2559 : nat) (m : nat) (P : nat -> Prop) (h1 : term208 m P) : term370 m P _2559.
Proof. exact (EQ_MP (@lem123115 m P _2559) (@lem123114 _2559 m P h1)). Qed.
Lemma lem123123 (_2562 : nat) (h1 : term324) : term553 _2562.
Proof. exact (@lem123002 h1 _2562). Qed.
Lemma lem123124 (_2562 : nat) : (term553 _2562) = (term348 _2562).
Proof. exact (eq_refl (term553 _2562)). Qed.
Lemma lem123125 (_2562 : nat) (h1 : term324) : term348 _2562.
Proof. exact (EQ_MP (@lem123124 _2562) (@lem123123 _2562 h1)). Qed.
Lemma lem123126 (_2562 : nat) (_2563 : nat) (h1 : term324) : term554 _2562 _2563.
Proof. exact (@lem123125 _2562 h1 _2563). Qed.
Lemma lem123127 (_2563 : nat) (_2562 : nat) : (term554 _2562 _2563) = (term346 _2563 _2562).
Proof. exact (eq_refl (term554 _2562 _2563)). Qed.
Lemma lem123132 (_2565 : nat) (h1 : term319) : term555 _2565.
Proof. exact (@lem123035 h1 _2565). Qed.
Lemma lem123133 (_2565 : nat) : (term555 _2565) = (term545 _2565).
Proof. exact (eq_refl (term555 _2565)). Qed.
Lemma lem123134 (_2565 : nat) (h1 : term319) : term545 _2565.
Proof. exact (EQ_MP (@lem123133 _2565) (@lem123132 _2565 h1)). Qed.
Lemma lem123135 (_2565 : nat) (_2566 : nat) (h1 : term319) : term556 _2565 _2566.
Proof. exact (@lem123134 _2565 h1 _2566). Qed.
Lemma lem123136 (_2565 : nat) (_2566 : nat) : (term556 _2565 _2566) = (term541 _2565 _2566).
Proof. exact (eq_refl (term556 _2565 _2566)). Qed.
Lemma lem123137 (_2565 : nat) (_2566 : nat) (h1 : term319) : term541 _2565 _2566.
Proof. exact (EQ_MP (@lem123136 _2565 _2566) (@lem123135 _2565 _2566 h1)). Qed.
Lemma lem123144 (_2569 : nat) (P : nat -> Prop) (m' : nat) (h1 : term397 P m') : term557 m' P _2569.
Proof. exact (@lem123070 P m' h1 _2569). Qed.
Lemma lem123145 (m' : nat) (P : nat -> Prop) (_2569 : nat) : (term557 m' P _2569) = (term391 m' P _2569).
Proof. exact (eq_refl (term557 m' P _2569)). Qed.
Lemma lem123158 (_2546 : nat) (m : nat) (P : nat -> Prop) (h1 : term225 m P) : term362 m P _2546.
Proof. exact (EQ_MP (@lem123076 m P _2546) (@lem123075 _2546 m P h1)). Qed.
Lemma lem123176 (_2548 : nat) (_2549 : nat) (h1 : term359) : term474 _2548 _2549.
Proof. exact (EQ_MP (@lem123085 _2548 _2549) (@lem123084 _2548 _2549 h1)). Qed.
Lemma lem123198 (_2557 : nat) (P : nat -> Prop) (n : nat -> nat) (h1 : term431 P n) : term558 P n _2557.
Proof. exact (proj2 (@lem123110 _2557 P n h1)). Qed.
Lemma lem123216 (_2558 : nat) (m : nat) (P : nat -> Prop) (h1 : term225 m P) : term362 m P _2558.
Proof. exact (EQ_MP (@lem123112 m P _2558) (@lem123111 _2558 m P h1)). Qed.
Lemma lem123227 (m : nat) (P : nat -> Prop) (_2559 : nat) : (term370 m P _2559) = (term559 m P _2559).
Proof. exact (@lem120119 (term543 _2559 m) (term560 P _2559) (P _2559)). Qed.
Lemma lem123228 (_2559 : nat) (m : nat) (P : nat -> Prop) (h1 : term208 m P) : term559 m P _2559.
Proof. exact (EQ_MP (@lem123227 m P _2559) (@lem123116 _2559 m P h1)). Qed.
Lemma lem123240 (_2563 : nat) (_2562 : nat) (h1 : term324) : term346 _2563 _2562.
Proof. exact (EQ_MP (@lem123127 _2563 _2562) (@lem123126 _2562 _2563 h1)). Qed.
Lemma lem123258 (_2569 : nat) (P : nat -> Prop) (m' : nat) (h1 : term397 P m') : term391 m' P _2569.
Proof. exact (EQ_MP (@lem123145 m' P _2569) (@lem123144 _2569 P m' h1)). Qed.
Lemma lem123260 (P : nat -> Prop) (m' : nat) (h1 : term397 P m') : term231 P m'.
Proof. exact (proj2 (@lem122806 P m' h1)). Qed.
Lemma lem123266 (_2565 : nat) (_2566 : nat) (h1 : term319) : term561 _2565 _2566.
Proof. exact (proj1 (@lem123137 _2565 _2566 h1)). Qed.
Lemma lem123350 (_2557 : nat) (P : nat -> Prop) (n : nat -> nat) (h1 : term431 P n) : term562 n _2557.
Proof. exact (proj1 (@lem123110 _2557 P n h1)). Qed.
Lemma lem123351 (m : nat) (P : nat -> Prop) (n : nat -> nat) (h1 : term431 P n) : term562 n m.
Proof. exact (@lem123350 m P n h1). Qed.
Lemma lem123352 (m : nat) (P : nat -> Prop) (n : nat -> nat) (h1 : term431 P n) : term563 n m.
Proof. exact (fun h0 : term564 n m => @lem123351 m P n h1). Qed.
Lemma lem123354 (p : Prop) : (term186 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem123355 (n : nat -> nat) (m : nat) : (term563 n m) = (term562 n m).
Proof. exact (@lem123354 (term562 n m)). Qed.
Lemma lem123356 (m : nat) (P : nat -> Prop) (n : nat -> nat) (h1 : term431 P n) : term562 n m.
Proof. exact (EQ_MP (@lem123355 n m) (@lem123352 m P n h1)). Qed.
Lemma lem123362 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem123363 (_2548 : nat) (_2549 : nat) : (term474 _2548 _2549) = (term565 _2548 _2549).
Proof. exact (@lem123362 (Peano.le _2548 _2549) (term543 _2548 _2549)). Qed.
Lemma lem123369 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem123370 (_2548 : nat) (_2549 : nat) : (term566 _2548 _2549) = (term567 _2548 _2549).
Proof. exact (MK_COMB (@lem123369) (@lem123363 _2548 _2549)). Qed.
Lemma lem123376 (_2548 : nat) (_2549 : nat) : (term565 _2548 _2549) = (term565 _2548 _2549).
Proof. exact (eq_refl (term565 _2548 _2549)). Qed.
Lemma lem123377 (_2548 : nat) (_2549 : nat) : ((term474 _2548 _2549) = (term565 _2548 _2549)) = ((term565 _2548 _2549) = (term565 _2548 _2549)).
Proof. exact (MK_COMB (@lem123370 _2548 _2549) (@lem123376 _2548 _2549)). Qed.
Lemma lem123379 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem123380 (x : Prop) : (x = x) = True.
Proof. exact (@lem123379 Prop x). Qed.
Lemma lem123381 (_2548 : nat) (_2549 : nat) : ((term565 _2548 _2549) = (term565 _2548 _2549)) = True.
Proof. exact (@lem123380 (term565 _2548 _2549)). Qed.
Lemma lem123382 (_2548 : nat) (_2549 : nat) : ((term474 _2548 _2549) = (term565 _2548 _2549)) = True.
Proof. exact (TRANS (@lem123377 _2548 _2549) (@lem123381 _2548 _2549)). Qed.
Lemma lem123383 (_2548 : nat) (_2549 : nat) : True = ((term474 _2548 _2549) = (term565 _2548 _2549)).
Proof. exact (SYM (@lem123382 _2548 _2549)). Qed.
Lemma lem123384 (_2548 : nat) (_2549 : nat) : (term474 _2548 _2549) = (term565 _2548 _2549).
Proof. exact (EQ_MP (@lem123383 _2548 _2549) (@lem0)). Qed.
Lemma lem123385 (_2548 : nat) (_2549 : nat) (h1 : term359) : term565 _2548 _2549.
Proof. exact (EQ_MP (@lem123384 _2548 _2549) (@lem123176 _2548 _2549 h1)). Qed.
Lemma lem123387 (b : Prop) (a : Prop) : (a \/ b) = (term38 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem123388 (_2548 : nat) (_2549 : nat) : (term565 _2548 _2549) = (term568 _2548 _2549).
Proof. exact (@lem123387 (term543 _2548 _2549) (Peano.le _2548 _2549)). Qed.
Lemma lem123390 (a : Prop) : (term47 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem123391 (_2548 : nat) (_2549 : nat) : (term569 _2548 _2549) = (Peano.lt _2548 _2549).
Proof. exact (@lem123390 (Peano.lt _2548 _2549)). Qed.
Lemma lem123392 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem123393 (_2548 : nat) (_2549 : nat) : (term570 _2548 _2549) = (term275 _2548 _2549).
Proof. exact (MK_COMB (@lem123392) (@lem123391 _2548 _2549)). Qed.
Lemma lem123394 (_2548 : nat) (_2549 : nat) : (Peano.le _2548 _2549) = (Peano.le _2548 _2549).
Proof. exact (eq_refl (Peano.le _2548 _2549)). Qed.
Lemma lem123395 (_2548 : nat) (_2549 : nat) : (term568 _2548 _2549) = (term355 _2548 _2549).
Proof. exact (MK_COMB (@lem123393 _2548 _2549) (@lem123394 _2548 _2549)). Qed.
Lemma lem123396 (_2548 : nat) (_2549 : nat) : (term565 _2548 _2549) = (term355 _2548 _2549).
Proof. exact (TRANS (@lem123388 _2548 _2549) (@lem123395 _2548 _2549)). Qed.
Lemma lem123399 (_2548 : nat) (_2549 : nat) (h1 : term359) : term355 _2548 _2549.
Proof. exact (EQ_MP (@lem123396 _2548 _2549) (@lem123385 _2548 _2549 h1)). Qed.
Lemma lem123400 (n : nat -> nat) (m : nat) (h1 : term359) : term571 n m.
Proof. exact (@lem123399 m (n m) h1). Qed.
Lemma lem123403 (m : nat) (P : nat -> Prop) (n : nat -> nat) (h1 : term359) (h2 : term431 P n) : term572 n m.
Proof. exact (@lem123400 n m h1 (@lem123356 m P n h2)). Qed.
Lemma lem123404 (m : nat) (P : nat -> Prop) (n : nat -> nat) (h1 : term359) (h2 : term431 P n) : term573 n m.
Proof. exact (fun h0 : term574 n m => @lem123403 m P n h1 h2). Qed.
Lemma lem123406 (p : Prop) : (term186 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem123407 (n : nat -> nat) (m : nat) : (term573 n m) = (term572 n m).
Proof. exact (@lem123406 (term572 n m)). Qed.
Lemma lem123408 (m : nat) (P : nat -> Prop) (n : nat -> nat) (h1 : term359) (h2 : term431 P n) : term572 n m.
Proof. exact (EQ_MP (@lem123407 n m) (@lem123404 m P n h1 h2)). Qed.
Lemma lem123414 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem123415 (P : nat -> Prop) (m : nat) (_2546 : nat) : (term362 m P _2546) = (term575 P m _2546).
Proof. exact (@lem123414 (P _2546) (term28 m _2546)). Qed.
Lemma lem123421 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem123422 (P : nat -> Prop) (m : nat) (_2546 : nat) : (term576 m P _2546) = (term577 P m _2546).
Proof. exact (MK_COMB (@lem123421) (@lem123415 P m _2546)). Qed.
Lemma lem123428 (P : nat -> Prop) (m : nat) (_2546 : nat) : (term575 P m _2546) = (term575 P m _2546).
Proof. exact (eq_refl (term575 P m _2546)). Qed.
Lemma lem123429 (P : nat -> Prop) (m : nat) (_2546 : nat) : ((term362 m P _2546) = (term575 P m _2546)) = ((term575 P m _2546) = (term575 P m _2546)).
Proof. exact (MK_COMB (@lem123422 P m _2546) (@lem123428 P m _2546)). Qed.
Lemma lem123431 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem123432 (x : Prop) : (x = x) = True.
Proof. exact (@lem123431 Prop x). Qed.
Lemma lem123433 (P : nat -> Prop) (m : nat) (_2546 : nat) : ((term575 P m _2546) = (term575 P m _2546)) = True.
Proof. exact (@lem123432 (term575 P m _2546)). Qed.
Lemma lem123434 (P : nat -> Prop) (m : nat) (_2546 : nat) : ((term362 m P _2546) = (term575 P m _2546)) = True.
Proof. exact (TRANS (@lem123429 P m _2546) (@lem123433 P m _2546)). Qed.
Lemma lem123435 (P : nat -> Prop) (m : nat) (_2546 : nat) : True = ((term362 m P _2546) = (term575 P m _2546)).
Proof. exact (SYM (@lem123434 P m _2546)). Qed.
Lemma lem123436 (P : nat -> Prop) (m : nat) (_2546 : nat) : (term362 m P _2546) = (term575 P m _2546).
Proof. exact (EQ_MP (@lem123435 P m _2546) (@lem0)). Qed.
Lemma lem123437 (_2546 : nat) (m : nat) (P : nat -> Prop) (h1 : term225 m P) : term575 P m _2546.
Proof. exact (EQ_MP (@lem123436 P m _2546) (@lem123158 _2546 m P h1)). Qed.
Lemma lem123439 (b : Prop) (a : Prop) : (a \/ b) = (term38 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem123440 (m : nat) (P : nat -> Prop) (_2546 : nat) : (term575 P m _2546) = (term578 m P _2546).
Proof. exact (@lem123439 (term28 m _2546) (P _2546)). Qed.
Lemma lem123442 (a : Prop) : (term47 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem123443 (m : nat) (_2546 : nat) : (term579 m _2546) = (Peano.le m _2546).
Proof. exact (@lem123442 (Peano.le m _2546)). Qed.
Lemma lem123444 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem123445 (m : nat) (_2546 : nat) : (term580 m _2546) = (term581 m _2546).
Proof. exact (MK_COMB (@lem123444) (@lem123443 m _2546)). Qed.
Lemma lem123446 (P : nat -> Prop) (_2546 : nat) : (P _2546) = (P _2546).
Proof. exact (eq_refl (P _2546)). Qed.
Lemma lem123447 (m : nat) (P : nat -> Prop) (_2546 : nat) : (term578 m P _2546) = (term360 m P _2546).
Proof. exact (MK_COMB (@lem123445 m _2546) (@lem123446 P _2546)). Qed.
Lemma lem123448 (m : nat) (P : nat -> Prop) (_2546 : nat) : (term575 P m _2546) = (term360 m P _2546).
Proof. exact (TRANS (@lem123440 m P _2546) (@lem123447 m P _2546)). Qed.
Lemma lem123451 (_2546 : nat) (m : nat) (P : nat -> Prop) (h1 : term225 m P) : term360 m P _2546.
Proof. exact (EQ_MP (@lem123448 m P _2546) (@lem123437 _2546 m P h1)). Qed.
Lemma lem123452 (n : nat -> nat) (m : nat) (P : nat -> Prop) (h1 : term225 m P) : term582 P n m.
Proof. exact (@lem123451 (n m) m P h1). Qed.
Lemma lem123455 (n : nat -> nat) (m : nat) (P : nat -> Prop) (h1 : term359) (h2 : term431 P n) (h3 : term225 m P) : term583 P n m.
Proof. exact (@lem123452 n m P h3 (@lem123408 m P n h1 h2)). Qed.
Lemma lem123456 (n : nat -> nat) (m : nat) (P : nat -> Prop) (h1 : term359) (h2 : term431 P n) (h3 : term225 m P) : term584 P n m.
Proof. exact (fun h0 : term558 P n m => @lem123455 n m P h1 h2 h3). Qed.
Lemma lem123458 (p : Prop) : (term186 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem123459 (P : nat -> Prop) (n : nat -> nat) (m : nat) : (term584 P n m) = (term583 P n m).
Proof. exact (@lem123458 (term583 P n m)). Qed.
Lemma lem123460 (n : nat -> nat) (m : nat) (P : nat -> Prop) (h1 : term359) (h2 : term431 P n) (h3 : term225 m P) : term583 P n m.
Proof. exact (EQ_MP (@lem123459 P n m) (@lem123456 n m P h1 h2 h3)). Qed.
Lemma lem123463 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem123465 (P : nat -> Prop) (n : nat -> nat) (_2557 : nat) : (term558 P n _2557) = (term585 P n _2557).
Proof. exact (@lem123463 (term583 P n _2557)). Qed.
Lemma lem123468 (_2557 : nat) (P : nat -> Prop) (n : nat -> nat) (h1 : term431 P n) : term585 P n _2557.
Proof. exact (EQ_MP (@lem123465 P n _2557) (@lem123198 _2557 P n h1)). Qed.
Lemma lem123469 (m : nat) (P : nat -> Prop) (n : nat -> nat) (h1 : term431 P n) : term585 P n m.
Proof. exact (@lem123468 m P n h1). Qed.
Lemma lem123472 (n : nat -> nat) (m : nat) (P : nat -> Prop) (h1 : term359) (h2 : term431 P n) (h3 : term225 m P) : False.
Proof. exact (@lem123469 m P n h2 (@lem123460 n m P h1 h2 h3)). Qed.
Lemma lem123473 (n : nat -> nat) (m : nat) (P : nat -> Prop) (h1 : term359) (h2 : term431 P n) (h3 : term225 m P) : term188.
Proof. exact (fun h0 : ~ False => @lem123472 n m P h1 h2 h3). Qed.
Lemma lem123475 (p : Prop) : (term186 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem123476 : term188 = False.
Proof. exact (@lem123475 False). Qed.
Lemma lem123477 (n : nat -> nat) (m : nat) (P : nat -> Prop) (h1 : term359) (h2 : term431 P n) (h3 : term225 m P) : False.
Proof. exact (EQ_MP (@lem123476) (@lem123473 n m P h1 h2 h3)). Qed.
Lemma lem123547 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem123548 (m' : nat) : m' = m'.
Proof. exact (@lem123547 m'). Qed.
Lemma lem123549 (m' : nat) : term586 m'.
Proof. exact (fun h0 : term587 m' => @lem123548 m'). Qed.
Lemma lem123551 (p : Prop) : (term186 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem123552 (m' : nat) : (term586 m') = (m' = m').
Proof. exact (@lem123551 (m' = m')). Qed.
Lemma lem123553 (m' : nat) : m' = m'.
Proof. exact (EQ_MP (@lem123552 m') (@lem123549 m')). Qed.
Lemma lem123555 (b : Prop) (a : Prop) : (a \/ b) = (term38 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem123556 (_2565 : nat) (_2566 : nat) : (term561 _2565 _2566) = (term588 _2565 _2566).
Proof. exact (@lem123555 (term542 _2565 _2566) (term350 _2565 _2566)). Qed.
Lemma lem123558 (a : Prop) : (term47 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem123559 (_2565 : nat) (_2566 : nat) : (term589 _2565 _2566) = (_2565 = _2566).
Proof. exact (@lem123558 (_2565 = _2566)). Qed.
Lemma lem123560 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem123561 (_2565 : nat) (_2566 : nat) : (term590 _2565 _2566) = (term591 _2565 _2566).
Proof. exact (MK_COMB (@lem123560) (@lem123559 _2565 _2566)). Qed.
Lemma lem123562 (_2565 : nat) (_2566 : nat) : (term350 _2565 _2566) = (term350 _2565 _2566).
Proof. exact (eq_refl (term350 _2565 _2566)). Qed.
Lemma lem123563 (_2565 : nat) (_2566 : nat) : (term588 _2565 _2566) = (term592 _2565 _2566).
Proof. exact (MK_COMB (@lem123561 _2565 _2566) (@lem123562 _2565 _2566)). Qed.
Lemma lem123564 (_2565 : nat) (_2566 : nat) : (term561 _2565 _2566) = (term592 _2565 _2566).
Proof. exact (TRANS (@lem123556 _2565 _2566) (@lem123563 _2565 _2566)). Qed.
Lemma lem123567 (_2565 : nat) (_2566 : nat) (h1 : term319) : term592 _2565 _2566.
Proof. exact (EQ_MP (@lem123564 _2565 _2566) (@lem123266 _2565 _2566 h1)). Qed.
Lemma lem123568 (m' : nat) (h1 : term319) : term593 m'.
Proof. exact (@lem123567 m' m' h1). Qed.
Lemma lem123571 (m' : nat) (h1 : term319) : term594 m'.
Proof. exact (@lem123568 m' h1 (@lem123553 m')). Qed.
Lemma lem123572 (m' : nat) (h1 : term319) : term595 m'.
Proof. exact (fun h0 : term596 m' => @lem123571 m' h1). Qed.
Lemma lem123574 (p : Prop) : (term186 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem123575 (m' : nat) : (term595 m') = (term594 m').
Proof. exact (@lem123574 (term594 m')). Qed.
Lemma lem123576 (m' : nat) (h1 : term319) : term594 m'.
Proof. exact (EQ_MP (@lem123575 m') (@lem123572 m' h1)). Qed.
Lemma lem123582 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem123583 (P : nat -> Prop) (m' : nat) (_2569 : nat) : (term391 m' P _2569) = (term597 P m' _2569).
Proof. exact (@lem123582 (P _2569) (term543 m' _2569)). Qed.
Lemma lem123589 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem123590 (P : nat -> Prop) (m' : nat) (_2569 : nat) : (term598 m' P _2569) = (term599 P m' _2569).
Proof. exact (MK_COMB (@lem123589) (@lem123583 P m' _2569)). Qed.
Lemma lem123596 (P : nat -> Prop) (m' : nat) (_2569 : nat) : (term597 P m' _2569) = (term597 P m' _2569).
Proof. exact (eq_refl (term597 P m' _2569)). Qed.
Lemma lem123597 (P : nat -> Prop) (m' : nat) (_2569 : nat) : ((term391 m' P _2569) = (term597 P m' _2569)) = ((term597 P m' _2569) = (term597 P m' _2569)).
Proof. exact (MK_COMB (@lem123590 P m' _2569) (@lem123596 P m' _2569)). Qed.
Lemma lem123599 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem123600 (x : Prop) : (x = x) = True.
Proof. exact (@lem123599 Prop x). Qed.
Lemma lem123601 (P : nat -> Prop) (m' : nat) (_2569 : nat) : ((term597 P m' _2569) = (term597 P m' _2569)) = True.
Proof. exact (@lem123600 (term597 P m' _2569)). Qed.
Lemma lem123602 (P : nat -> Prop) (m' : nat) (_2569 : nat) : ((term391 m' P _2569) = (term597 P m' _2569)) = True.
Proof. exact (TRANS (@lem123597 P m' _2569) (@lem123601 P m' _2569)). Qed.
Lemma lem123603 (P : nat -> Prop) (m' : nat) (_2569 : nat) : True = ((term391 m' P _2569) = (term597 P m' _2569)).
Proof. exact (SYM (@lem123602 P m' _2569)). Qed.
Lemma lem123604 (P : nat -> Prop) (m' : nat) (_2569 : nat) : (term391 m' P _2569) = (term597 P m' _2569).
Proof. exact (EQ_MP (@lem123603 P m' _2569) (@lem0)). Qed.
Lemma lem123605 (_2569 : nat) (P : nat -> Prop) (m' : nat) (h1 : term397 P m') : term597 P m' _2569.
Proof. exact (EQ_MP (@lem123604 P m' _2569) (@lem123258 _2569 P m' h1)). Qed.
Lemma lem123607 (b : Prop) (a : Prop) : (a \/ b) = (term38 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem123608 (m' : nat) (P : nat -> Prop) (_2569 : nat) : (term597 P m' _2569) = (term600 m' P _2569).
Proof. exact (@lem123607 (term543 m' _2569) (P _2569)). Qed.
Lemma lem123610 (a : Prop) : (term47 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem123611 (m' : nat) (_2569 : nat) : (term569 m' _2569) = (Peano.lt m' _2569).
Proof. exact (@lem123610 (Peano.lt m' _2569)). Qed.
Lemma lem123612 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem123613 (m' : nat) (_2569 : nat) : (term570 m' _2569) = (term275 m' _2569).
Proof. exact (MK_COMB (@lem123612) (@lem123611 m' _2569)). Qed.
Lemma lem123614 (P : nat -> Prop) (_2569 : nat) : (P _2569) = (P _2569).
Proof. exact (eq_refl (P _2569)). Qed.
Lemma lem123615 (m' : nat) (P : nat -> Prop) (_2569 : nat) : (term600 m' P _2569) = (term276 m' P _2569).
Proof. exact (MK_COMB (@lem123613 m' _2569) (@lem123614 P _2569)). Qed.
Lemma lem123616 (m' : nat) (P : nat -> Prop) (_2569 : nat) : (term597 P m' _2569) = (term276 m' P _2569).
Proof. exact (TRANS (@lem123608 m' P _2569) (@lem123615 m' P _2569)). Qed.
Lemma lem123619 (_2569 : nat) (P : nat -> Prop) (m' : nat) (h1 : term397 P m') : term276 m' P _2569.
Proof. exact (EQ_MP (@lem123616 m' P _2569) (@lem123605 _2569 P m' h1)). Qed.
Lemma lem123620 (P : nat -> Prop) (m' : nat) (h1 : term397 P m') : term601 P m'.
Proof. exact (@lem123619 (S m') P m' h1). Qed.
Lemma lem123623 (P : nat -> Prop) (m' : nat) (h1 : term319) (h2 : term397 P m') : term197 P m'.
Proof. exact (@lem123620 P m' h2 (@lem123576 m' h1)). Qed.
Lemma lem123624 (P : nat -> Prop) (m' : nat) (h1 : term319) (h2 : term397 P m') : term602 P m'.
Proof. exact (fun h0 : term560 P m' => @lem123623 P m' h1 h2). Qed.
Lemma lem123626 (p : Prop) : (term186 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem123627 (P : nat -> Prop) (m' : nat) : (term602 P m') = (term197 P m').
Proof. exact (@lem123626 (term197 P m')). Qed.
Lemma lem123628 (P : nat -> Prop) (m' : nat) (h1 : term319) (h2 : term397 P m') : term197 P m'.
Proof. exact (EQ_MP (@lem123627 P m') (@lem123624 P m' h1 h2)). Qed.
Lemma lem123631 (P : nat -> Prop) (m' : nat) (h1 : term231 P m') : term231 P m'.
Proof. exact (h1). Qed.
Lemma lem123632 (P : nat -> Prop) (m' : nat) (h1 : term231 P m') : term603 P m'.
Proof. exact (fun h0 : P m' => @lem123631 P m' h1). Qed.
Lemma lem123634 (p : Prop) : (term76 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem123635 (P : nat -> Prop) (m' : nat) : (term603 P m') = (term231 P m').
Proof. exact (@lem123634 (P m')). Qed.
Lemma lem123636 (P : nat -> Prop) (m' : nat) (h1 : term231 P m') : term231 P m'.
Proof. exact (EQ_MP (@lem123635 P m') (@lem123632 P m' h1)). Qed.
Lemma lem123638 (b : Prop) (a : Prop) : (a \/ b) = (term38 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem123639 (P : nat -> Prop) (_2559 : nat) (m : nat) : (term559 m P _2559) = (term604 P _2559 m).
Proof. exact (@lem123638 (term605 P _2559) (term543 _2559 m)). Qed.
Lemma lem123641 (a : Prop) (b : Prop) : (term606 a b) = (term607 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem123642 (P : nat -> Prop) (_2559 : nat) : (term608 P _2559) = (term609 P _2559).
Proof. exact (@lem123641 (term560 P _2559) (P _2559)). Qed.
Lemma lem123644 (a : Prop) : (term47 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem123645 (P : nat -> Prop) (_2559 : nat) : (term610 P _2559) = (term197 P _2559).
Proof. exact (@lem123644 (term197 P _2559)). Qed.
Lemma lem123646 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem123647 (P : nat -> Prop) (_2559 : nat) : (term611 P _2559) = (term612 P _2559).
Proof. exact (MK_COMB (@lem123646) (@lem123645 P _2559)). Qed.
Lemma lem123648 (P : nat -> Prop) (_2559 : nat) : (term231 P _2559) = (term231 P _2559).
Proof. exact (eq_refl (term231 P _2559)). Qed.
Lemma lem123649 (P : nat -> Prop) (_2559 : nat) : (term609 P _2559) = (term613 P _2559).
Proof. exact (MK_COMB (@lem123647 P _2559) (@lem123648 P _2559)). Qed.
Lemma lem123650 (P : nat -> Prop) (_2559 : nat) : (term608 P _2559) = (term613 P _2559).
Proof. exact (TRANS (@lem123642 P _2559) (@lem123649 P _2559)). Qed.
Lemma lem123651 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem123652 (P : nat -> Prop) (_2559 : nat) : (term614 P _2559) = (term615 P _2559).
Proof. exact (MK_COMB (@lem123651) (@lem123650 P _2559)). Qed.
Lemma lem123653 (_2559 : nat) (m : nat) : (term543 _2559 m) = (term543 _2559 m).
Proof. exact (eq_refl (term543 _2559 m)). Qed.
Lemma lem123654 (P : nat -> Prop) (_2559 : nat) (m : nat) : (term604 P _2559 m) = (term616 P _2559 m).
Proof. exact (MK_COMB (@lem123652 P _2559) (@lem123653 _2559 m)). Qed.
Lemma lem123655 (P : nat -> Prop) (_2559 : nat) (m : nat) : (term559 m P _2559) = (term616 P _2559 m).
Proof. exact (TRANS (@lem123639 P _2559 m) (@lem123654 P _2559 m)). Qed.
Lemma lem123657 (P : nat -> Prop) (m' : nat) (h1 : term231 P m') (h2 : term319) (h3 : term397 P m') : term613 P m'.
Proof. exact (conj (@lem123628 P m' h2 h3) (@lem123636 P m' h1)). Qed.
Lemma lem123659 (_2559 : nat) (m : nat) (P : nat -> Prop) (h1 : term208 m P) : term616 P _2559 m.
Proof. exact (EQ_MP (@lem123655 P _2559 m) (@lem123228 _2559 m P h1)). Qed.
Lemma lem123660 (m' : nat) (m : nat) (P : nat -> Prop) (h1 : term208 m P) : term616 P m' m.
Proof. exact (@lem123659 m' m P h1). Qed.
Lemma lem123663 (m : nat) (P : nat -> Prop) (m' : nat) (h1 : term208 m P) (h2 : term231 P m') (h3 : term319) (h4 : term397 P m') : term543 m' m.
Proof. exact (@lem123660 m' m P h1 (@lem123657 P m' h2 h3 h4)). Qed.
Lemma lem123664 (m : nat) (P : nat -> Prop) (m' : nat) (h1 : term208 m P) (h2 : term231 P m') (h3 : term319) (h4 : term397 P m') : term617 m' m.
Proof. exact (fun h0 : Peano.lt m' m => @lem123663 m P m' h1 h2 h3 h4). Qed.
Lemma lem123666 (p : Prop) : (term76 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem123667 (m' : nat) (m : nat) : (term617 m' m) = (term543 m' m).
Proof. exact (@lem123666 (Peano.lt m' m)). Qed.
Lemma lem123668 (m : nat) (P : nat -> Prop) (m' : nat) (h1 : term208 m P) (h2 : term231 P m') (h3 : term319) (h4 : term397 P m') : term543 m' m.
Proof. exact (EQ_MP (@lem123667 m' m) (@lem123664 m P m' h1 h2 h3 h4)). Qed.
Lemma lem123679 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem123680 (_2563 : nat) (_2562 : nat) : (term618 _2562 _2563) = (term346 _2563 _2562).
Proof. exact (@lem123679 (Peano.lt _2562 _2563) (Peano.le _2563 _2562)). Qed.
Lemma lem123686 (_2563 : nat) (_2562 : nat) : (term619 _2563 _2562) = (term619 _2563 _2562).
Proof. exact (eq_refl (term619 _2563 _2562)). Qed.
Lemma lem123687 (_2563 : nat) (_2562 : nat) : ((term346 _2563 _2562) = (term618 _2562 _2563)) = ((term346 _2563 _2562) = (term346 _2563 _2562)).
Proof. exact (MK_COMB (@lem123686 _2563 _2562) (@lem123680 _2563 _2562)). Qed.
Lemma lem123689 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem123690 (x : Prop) : (x = x) = True.
Proof. exact (@lem123689 Prop x). Qed.
Lemma lem123691 (_2563 : nat) (_2562 : nat) : ((term346 _2563 _2562) = (term346 _2563 _2562)) = True.
Proof. exact (@lem123690 (term346 _2563 _2562)). Qed.
Lemma lem123692 (_2562 : nat) (_2563 : nat) : ((term346 _2563 _2562) = (term618 _2562 _2563)) = True.
Proof. exact (TRANS (@lem123687 _2563 _2562) (@lem123691 _2563 _2562)). Qed.
Lemma lem123693 (_2562 : nat) (_2563 : nat) : True = ((term346 _2563 _2562) = (term618 _2562 _2563)).
Proof. exact (SYM (@lem123692 _2562 _2563)). Qed.
Lemma lem123694 (_2562 : nat) (_2563 : nat) : (term346 _2563 _2562) = (term618 _2562 _2563).
Proof. exact (EQ_MP (@lem123693 _2562 _2563) (@lem0)). Qed.
Lemma lem123695 (_2562 : nat) (_2563 : nat) (h1 : term324) : term618 _2562 _2563.
Proof. exact (EQ_MP (@lem123694 _2562 _2563) (@lem123240 _2563 _2562 h1)). Qed.
Lemma lem123697 (b : Prop) (a : Prop) : (a \/ b) = (term38 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem123700 (_2563 : nat) (_2562 : nat) : (term618 _2562 _2563) = (term620 _2563 _2562).
Proof. exact (@lem123697 (Peano.lt _2562 _2563) (Peano.le _2563 _2562)). Qed.
Lemma lem123703 (_2563 : nat) (_2562 : nat) (h1 : term324) : term620 _2563 _2562.
Proof. exact (EQ_MP (@lem123700 _2563 _2562) (@lem123695 _2562 _2563 h1)). Qed.
Lemma lem123704 (m : nat) (m' : nat) (h1 : term324) : term620 m m'.
Proof. exact (@lem123703 m m' h1). Qed.
Lemma lem123707 (m : nat) (P : nat -> Prop) (m' : nat) (h1 : term324) (h2 : term208 m P) (h3 : term231 P m') (h4 : term319) (h5 : term397 P m') : Peano.le m m'.
Proof. exact (@lem123704 m m' h1 (@lem123668 m P m' h2 h3 h4 h5)). Qed.
Lemma lem123708 (m : nat) (P : nat -> Prop) (m' : nat) (h1 : term324) (h2 : term208 m P) (h3 : term231 P m') (h4 : term319) (h5 : term397 P m') : term621 m m'.
Proof. exact (fun h0 : term28 m m' => @lem123707 m P m' h1 h2 h3 h4 h5). Qed.
Lemma lem123710 (p : Prop) : (term186 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem123711 (m : nat) (m' : nat) : (term621 m m') = (Peano.le m m').
Proof. exact (@lem123710 (Peano.le m m')). Qed.
Lemma lem123712 (m : nat) (P : nat -> Prop) (m' : nat) (h1 : term324) (h2 : term208 m P) (h3 : term231 P m') (h4 : term319) (h5 : term397 P m') : Peano.le m m'.
Proof. exact (EQ_MP (@lem123711 m m') (@lem123708 m P m' h1 h2 h3 h4 h5)). Qed.
Lemma lem123718 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem123719 (P : nat -> Prop) (m : nat) (_2558 : nat) : (term362 m P _2558) = (term575 P m _2558).
Proof. exact (@lem123718 (P _2558) (term28 m _2558)). Qed.
Lemma lem123725 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem123726 (P : nat -> Prop) (m : nat) (_2558 : nat) : (term576 m P _2558) = (term577 P m _2558).
Proof. exact (MK_COMB (@lem123725) (@lem123719 P m _2558)). Qed.
Lemma lem123732 (P : nat -> Prop) (m : nat) (_2558 : nat) : (term575 P m _2558) = (term575 P m _2558).
Proof. exact (eq_refl (term575 P m _2558)). Qed.
Lemma lem123733 (P : nat -> Prop) (m : nat) (_2558 : nat) : ((term362 m P _2558) = (term575 P m _2558)) = ((term575 P m _2558) = (term575 P m _2558)).
Proof. exact (MK_COMB (@lem123726 P m _2558) (@lem123732 P m _2558)). Qed.
Lemma lem123735 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem123736 (x : Prop) : (x = x) = True.
Proof. exact (@lem123735 Prop x). Qed.
Lemma lem123737 (P : nat -> Prop) (m : nat) (_2558 : nat) : ((term575 P m _2558) = (term575 P m _2558)) = True.
Proof. exact (@lem123736 (term575 P m _2558)). Qed.
Lemma lem123738 (P : nat -> Prop) (m : nat) (_2558 : nat) : ((term362 m P _2558) = (term575 P m _2558)) = True.
Proof. exact (TRANS (@lem123733 P m _2558) (@lem123737 P m _2558)). Qed.
Lemma lem123739 (P : nat -> Prop) (m : nat) (_2558 : nat) : True = ((term362 m P _2558) = (term575 P m _2558)).
Proof. exact (SYM (@lem123738 P m _2558)). Qed.
Lemma lem123740 (P : nat -> Prop) (m : nat) (_2558 : nat) : (term362 m P _2558) = (term575 P m _2558).
Proof. exact (EQ_MP (@lem123739 P m _2558) (@lem0)). Qed.
Lemma lem123741 (_2558 : nat) (m : nat) (P : nat -> Prop) (h1 : term225 m P) : term575 P m _2558.
Proof. exact (EQ_MP (@lem123740 P m _2558) (@lem123216 _2558 m P h1)). Qed.
Lemma lem123743 (b : Prop) (a : Prop) : (a \/ b) = (term38 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem123744 (m : nat) (P : nat -> Prop) (_2558 : nat) : (term575 P m _2558) = (term578 m P _2558).
Proof. exact (@lem123743 (term28 m _2558) (P _2558)). Qed.
Lemma lem123746 (a : Prop) : (term47 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem123747 (m : nat) (_2558 : nat) : (term579 m _2558) = (Peano.le m _2558).
Proof. exact (@lem123746 (Peano.le m _2558)). Qed.
Lemma lem123748 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem123749 (m : nat) (_2558 : nat) : (term580 m _2558) = (term581 m _2558).
Proof. exact (MK_COMB (@lem123748) (@lem123747 m _2558)). Qed.
Lemma lem123750 (P : nat -> Prop) (_2558 : nat) : (P _2558) = (P _2558).
Proof. exact (eq_refl (P _2558)). Qed.
Lemma lem123751 (m : nat) (P : nat -> Prop) (_2558 : nat) : (term578 m P _2558) = (term360 m P _2558).
Proof. exact (MK_COMB (@lem123749 m _2558) (@lem123750 P _2558)). Qed.
Lemma lem123752 (m : nat) (P : nat -> Prop) (_2558 : nat) : (term575 P m _2558) = (term360 m P _2558).
Proof. exact (TRANS (@lem123744 m P _2558) (@lem123751 m P _2558)). Qed.
Lemma lem123755 (_2558 : nat) (m : nat) (P : nat -> Prop) (h1 : term225 m P) : term360 m P _2558.
Proof. exact (EQ_MP (@lem123752 m P _2558) (@lem123741 _2558 m P h1)). Qed.
Lemma lem123756 (m' : nat) (m : nat) (P : nat -> Prop) (h1 : term225 m P) : term360 m P m'.
Proof. exact (@lem123755 m' m P h1). Qed.
Lemma lem123759 (m : nat) (P : nat -> Prop) (m' : nat) (h1 : term324) (h2 : term208 m P) (h3 : term225 m P) (h4 : term231 P m') (h5 : term319) (h6 : term397 P m') : P m'.
Proof. exact (@lem123756 m' m P h3 (@lem123712 m P m' h1 h2 h4 h5 h6)). Qed.
Lemma lem123760 (m : nat) (P : nat -> Prop) (m' : nat) (h1 : term324) (h2 : term208 m P) (h3 : term225 m P) (h4 : term319) (h5 : term397 P m') : term622 P m'.
Proof. exact (fun h0 : term231 P m' => @lem123759 m P m' h1 h2 h3 h0 h4 h5). Qed.
Lemma lem123762 (p : Prop) : (term186 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem123763 (P : nat -> Prop) (m' : nat) : (term622 P m') = (P m').
Proof. exact (@lem123762 (P m')). Qed.
Lemma lem123764 (m : nat) (P : nat -> Prop) (m' : nat) (h1 : term324) (h2 : term208 m P) (h3 : term225 m P) (h4 : term319) (h5 : term397 P m') : P m'.
Proof. exact (EQ_MP (@lem123763 P m') (@lem123760 m P m' h1 h2 h3 h4 h5)). Qed.
Lemma lem123767 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem123769 (P : nat -> Prop) (m' : nat) : (term231 P m') = (term623 P m').
Proof. exact (@lem123767 (P m')). Qed.
Lemma lem123772 (P : nat -> Prop) (m' : nat) (h1 : term397 P m') : term623 P m'.
Proof. exact (EQ_MP (@lem123769 P m') (@lem123260 P m' h1)). Qed.
Lemma lem123775 (m : nat) (P : nat -> Prop) (m' : nat) (h1 : term324) (h2 : term208 m P) (h3 : term225 m P) (h4 : term319) (h5 : term397 P m') : False.
Proof. exact (@lem123772 P m' h5 (@lem123764 m P m' h1 h2 h3 h4 h5)). Qed.
Lemma lem123776 (m : nat) (P : nat -> Prop) (m' : nat) (h1 : term324) (h2 : term208 m P) (h3 : term225 m P) (h4 : term319) (h5 : term397 P m') : term188.
Proof. exact (fun h0 : ~ False => @lem123775 m P m' h1 h2 h3 h4 h5). Qed.
Lemma lem123778 (p : Prop) : (term186 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem123779 : term188 = False.
Proof. exact (@lem123778 False). Qed.
Lemma lem123780 (m : nat) (P : nat -> Prop) (m' : nat) (h1 : term324) (h2 : term208 m P) (h3 : term225 m P) (h4 : term319) (h5 : term397 P m') : False.
Proof. exact (EQ_MP (@lem123779) (@lem123776 m P m' h1 h2 h3 h4 h5)). Qed.
Lemma lem123781 (m : nat) (P : nat -> Prop) (m' : nat) (h1 : term324) (h2 : term208 m P) (h3 : term225 m P) (h4 : term319) (h5 : term397 P m') : term324 = False.
Proof. exact (prop_ext (fun h6 : term324 => @lem123780 m P m' h1 h2 h3 h4 h5) (fun h6 : False => @lem123002 h1)). Qed.
Lemma lem123782 (m : nat) (P : nat -> Prop) (m' : nat) (h1 : term324) (h2 : term208 m P) (h3 : term225 m P) (h4 : term319) (h5 : term397 P m') : False.
Proof. exact (EQ_MP (@lem123781 m P m' h1 h2 h3 h4 h5) (@lem123002 h1)). Qed.
Lemma lem123783 (n : nat -> nat) (m : nat) (P : nat -> Prop) (h1 : term359) (h2 : term431 P n) (h3 : term225 m P) : (term431 P n) = False.
Proof. exact (prop_ext (fun h4 : term431 P n => @lem123477 n m P h1 h2 h3) (fun h4 : False => @lem122938 P n h2)). Qed.
Lemma lem123784 (n : nat -> nat) (m : nat) (P : nat -> Prop) (h1 : term359) (h2 : term431 P n) (h3 : term225 m P) : False.
Proof. exact (EQ_MP (@lem123783 n m P h1 h2 h3) (@lem122938 P n h2)). Qed.
Lemma lem123785 (m : nat) (n : nat -> nat) (P : nat -> Prop) (m' : nat) (h1 : term359) (h2 : term324) (h3 : term208 m P) (h4 : term225 m P) (h5 : term319) (h6 : term468 n P m') : False.
Proof. exact (or_elim (@lem122800 n P m' h6) (fun h0 : term431 P n => @lem123784 n m P h1 h0 h4) (fun h0 : term397 P m' => @lem123782 m P m' h2 h3 h4 h5 h0)). Qed.
Lemma lem123786 (m : nat) (n : nat -> nat) (P : nat -> Prop) (m' : nat) (h1 : term359) (h2 : term324) (h3 : term208 m P) (h4 : term225 m P) (h5 : term319) (h6 : term468 n P m') : (term468 n P m') = False.
Proof. exact (prop_ext (fun h7 : term468 n P m' => @lem123785 m n P m' h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem122800 n P m' h6)). Qed.
Lemma lem123787 (m : nat) (n : nat -> nat) (P : nat -> Prop) (m' : nat) (h1 : term359) (h2 : term324) (h3 : term208 m P) (h4 : term225 m P) (h5 : term319) (h6 : term468 n P m') : False.
Proof. exact (EQ_MP (@lem123786 m n P m' h1 h2 h3 h4 h5 h6) (@lem122800 n P m' h6)). Qed.
Lemma lem123788 (m : nat) (n : nat -> nat) (P : nat -> Prop) (m' : nat) (h1 : term359) (h2 : term324) (h3 : term208 m P) (h4 : term225 m P) (h5 : term319) (h6 : term468 n P m') : term324 = False.
Proof. exact (prop_ext (fun h7 : term324 => @lem123787 m n P m' h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem122752 h2)). Qed.
Lemma lem123789 (m : nat) (n : nat -> nat) (P : nat -> Prop) (m' : nat) (h1 : term359) (h2 : term324) (h3 : term208 m P) (h4 : term225 m P) (h5 : term319) (h6 : term468 n P m') : False.
Proof. exact (EQ_MP (@lem123788 m n P m' h1 h2 h3 h4 h5 h6) (@lem122752 h2)). Qed.
Lemma lem123790 (m : nat) (n : nat -> nat) (P : nat -> Prop) (h1 : term359) (h2 : term324) (h3 : term208 m P) (h4 : term225 m P) (h5 : term471 n P) (h6 : term319) : False.
Proof. exact (ex_elim (@lem122582 n P h5) (fun m' : nat => fun h0 : term470 n P m' => @lem123789 m n P m' h1 h2 h3 h4 h6 h0)). Qed.
Lemma lem123791 (m : nat) (P : nat -> Prop) (h1 : term359) (h2 : term324) (h3 : term208 m P) (h4 : term225 m P) (h5 : term304 P) (h6 : term319) : False.
Proof. exact (ex_elim (@lem122133 P h5) (fun n : nat -> nat => fun h0 : term472 P n => @lem123790 m n P h1 h2 h3 h4 h0 h6)). Qed.
Lemma lem123792 (m : nat) (P : nat -> Prop) (h1 : term359) (h2 : term324) (h3 : term208 m P) (h4 : term225 m P) (h5 : term304 P) (h6 : term319) : term324 = False.
Proof. exact (prop_ext (fun h7 : term324 => @lem123791 m P h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem122581 h2)). Qed.
Lemma lem123793 (m : nat) (P : nat -> Prop) (h1 : term359) (h2 : term324) (h3 : term208 m P) (h4 : term225 m P) (h5 : term304 P) (h6 : term319) : False.
Proof. exact (EQ_MP (@lem123792 m P h1 h2 h3 h4 h5 h6) (@lem122581 h2)). Qed.
Lemma lem123794 (m : nat) (P : nat -> Prop) (h1 : term359) (h2 : term208 m P) (h3 : term225 m P) (h4 : term304 P) (h5 : term319) : term322.
Proof. exact (fun h0 : term324 => @lem123793 m P h1 h0 h2 h3 h4 h5). Qed.
Lemma lem123795 : term322 = term323.
Proof. exact (@lem69 term324). Qed.
Lemma lem123796 (m : nat) (P : nat -> Prop) (h1 : term359) (h2 : term208 m P) (h3 : term225 m P) (h4 : term304 P) (h5 : term319) : term323.
Proof. exact (EQ_MP (@lem123795) (@lem123794 m P h1 h2 h3 h4 h5)). Qed.
Lemma lem123797 (m : nat) (P : nat -> Prop) (h1 : term359) (h2 : term208 m P) (h3 : term225 m P) (h4 : term304 P) : term326.
Proof. exact (fun h0 : term319 => @lem123796 m P h1 h2 h3 h4 h0). Qed.
Lemma lem123798 (m : nat) (P : nat -> Prop) (h1 : term208 m P) (h2 : term225 m P) (h3 : term304 P) : term329.
Proof. exact (fun h0 : term359 => @lem123797 m P h0 h1 h2 h3). Qed.
Lemma lem123799 (m : nat) (P : nat -> Prop) (h1 : term208 m P) (h2 : term225 m P) : term332 P.
Proof. exact (fun h0 : term304 P => @lem123798 m P h1 h2 h0). Qed.
Lemma lem123800 (m : nat) (P : nat -> Prop) (h1 : term225 m P) : term335 m P.
Proof. exact (fun h0 : term208 m P => @lem123799 m P h0 h1). Qed.
Lemma lem123801 (m : nat) (P : nat -> Prop) : term337 m P.
Proof. exact (fun h0 : term225 m P => @lem123800 m P h0). Qed.
Lemma lem123806 (P : nat -> Prop) : term341 P.
Proof. exact (fun m : nat => @lem123801 m P). Qed.
Lemma lem123811 : term345.
Proof. exact (fun P : nat -> Prop => @lem123806 P). Qed.
Lemma lem123812 : term344.
Proof. exact (EQ_MP (@lem121748) (@lem123811)). Qed.
Lemma lem123813 (P : nat -> Prop) : term624 P.
Proof. exact (@lem123812 P). Qed.
Lemma lem123814 (P : nat -> Prop) : (term624 P) = (term340 P).
Proof. exact (eq_refl (term624 P)). Qed.
Lemma lem123815 (P : nat -> Prop) : term340 P.
Proof. exact (EQ_MP (@lem123814 P) (@lem123813 P)). Qed.
Lemma lem123816 (P : nat -> Prop) (m : nat) : term625 P m.
Proof. exact (@lem123815 P m). Qed.
Lemma lem123817 (m : nat) (P : nat -> Prop) : (term625 P m) = (term305 m P).
Proof. exact (eq_refl (term625 P m)). Qed.
Lemma lem123818 (m : nat) (P : nat -> Prop) : term305 m P.
Proof. exact (EQ_MP (@lem123817 m P) (@lem123816 P m)). Qed.
Lemma lem123820 (m : nat) (P : nat -> Prop) : term305 m P.
Proof. exact (@lem121308 m P (@lem123818 m P)). Qed.
Lemma lem123821 (m : nat) (P : nat -> Prop) (h1 : term225 m P) : term334 m P.
Proof. exact (@lem123820 m P (@lem121084 m P h1)). Qed.
Lemma lem123822 (m : nat) (P : nat -> Prop) (h1 : term208 m P) (h2 : term225 m P) : term331 P.
Proof. exact (@lem123821 m P h2 (@lem121083 m P h1)). Qed.
Lemma lem123823 (m : nat) (P : nat -> Prop) (h1 : term208 m P) (h2 : term225 m P) (h3 : term304 P) : term328.
Proof. exact (@lem123822 m P h1 h2 (@lem121293 P h3)). Qed.
Lemma lem123824 (m : nat) (P : nat -> Prop) (h1 : term208 m P) (h2 : term225 m P) (h3 : term304 P) : term325.
Proof. exact (@lem123823 m P h1 h2 h3 (@lem98439)). Qed.
Lemma lem123825 (m : nat) (P : nat -> Prop) (h1 : term208 m P) (h2 : term225 m P) (h3 : term304 P) : term322.
Proof. exact (@lem123824 m P h1 h2 h3 (@lem89997)). Qed.
Lemma lem123826 (m : nat) (P : nat -> Prop) (h1 : term208 m P) (h2 : term225 m P) (h3 : term304 P) : False.
Proof. exact (@lem123825 m P h1 h2 h3 (@lem96963)). Qed.
Lemma lem123827 (m : nat) (P : nat -> Prop) (h1 : term208 m P) (h2 : term225 m P) (h3 : term304 P) : (term304 P) = False.
Proof. exact (prop_ext (fun h4 : term304 P => @lem123826 m P h1 h2 h3) (fun h4 : False => @lem121293 P h3)). Qed.
Lemma lem123828 (m : nat) (P : nat -> Prop) (h1 : term208 m P) (h2 : term225 m P) (h3 : term304 P) : False.
Proof. exact (EQ_MP (@lem123827 m P h1 h2 h3) (@lem121293 P h3)). Qed.
Lemma lem123829 (m : nat) (P : nat -> Prop) (h1 : term208 m P) (h2 : term225 m P) : term303 P.
Proof. exact (fun h0 : term304 P => @lem123828 m P h1 h2 h0). Qed.
Lemma lem123830 (m : nat) (P : nat -> Prop) (h1 : term208 m P) (h2 : term225 m P) : term302 P.
Proof. exact (EQ_MP (@lem121292 P) (@lem123829 m P h1 h2)). Qed.
Lemma lem123831 (m : nat) (P : nat -> Prop) (h1 : term208 m P) (h2 : term225 m P) : term273 P.
Proof. exact (EQ_MP (@lem121288 P) (@lem123830 m P h1 h2)). Qed.
Lemma lem123832 (m : nat) (P : nat -> Prop) (h1 : term208 m P) (h2 : term225 m P) : term272 P.
Proof. exact (EQ_MP (@lem121181 P) (@lem123831 m P h1 h2)). Qed.
Lemma lem123833 (m : nat) (P : nat -> Prop) (h1 : term208 m P) (h2 : term225 m P) : term626 P.
Proof. exact (@lem121135 P (@lem123832 m P h1 h2)). Qed.
Lemma lem123834 (m : nat) (P : nat -> Prop) (h1 : term208 m P) (h2 : term225 m P) : term226 P.
Proof. exact (@lem123833 m P h1 h2 (@lem121132 P)). Qed.
Lemma lem123835 (m : nat) (P : nat -> Prop) (h1 : term208 m P) (h2 : term225 m P) : term214 P.
Proof. exact (EQ_MP (@lem121092 P) (@lem123834 m P h1 h2)). Qed.
Lemma lem123836 (m : nat) (P : nat -> Prop) (h1 : term211 m P) : term208 m P.
Proof. exact (proj2 (@lem121082 m P h1)). Qed.
Lemma lem123837 (m : nat) (P : nat -> Prop) (h1 : term211 m P) : term225 m P.
Proof. exact (proj1 (@lem121082 m P h1)). Qed.
Lemma lem123838 (m : nat) (P : nat -> Prop) (h1 : term208 m P) (h2 : term225 m P) : (term208 m P) = (term214 P).
Proof. exact (prop_ext (fun h3 : term208 m P => @lem123835 m P h1 h2) (fun h3 : term214 P => @lem121083 m P h1)). Qed.
Lemma lem123839 (m : nat) (P : nat -> Prop) (h1 : term208 m P) (h2 : term225 m P) : term214 P.
Proof. exact (EQ_MP (@lem123838 m P h1 h2) (@lem121083 m P h1)). Qed.
Lemma lem123840 (m : nat) (P : nat -> Prop) (h1 : term208 m P) (h2 : term225 m P) : (term225 m P) = (term214 P).
Proof. exact (prop_ext (fun h3 : term225 m P => @lem123839 m P h1 h2) (fun h3 : term214 P => @lem121084 m P h2)). Qed.
Lemma lem123841 (m : nat) (P : nat -> Prop) (h1 : term208 m P) (h2 : term225 m P) : term214 P.
Proof. exact (EQ_MP (@lem123840 m P h1 h2) (@lem121084 m P h2)). Qed.
Lemma lem123842 (m : nat) (P : nat -> Prop) (h1 : term225 m P) (h2 : term211 m P) : (term208 m P) = (term214 P).
Proof. exact (prop_ext (fun h3 : term208 m P => @lem123841 m P h3 h1) (fun h3 : term214 P => @lem123836 m P h2)). Qed.
Lemma lem123843 (m : nat) (P : nat -> Prop) (h1 : term225 m P) (h2 : term211 m P) : term214 P.
Proof. exact (EQ_MP (@lem123842 m P h1 h2) (@lem123836 m P h2)). Qed.
Lemma lem123844 (m : nat) (P : nat -> Prop) (h1 : term211 m P) : (term225 m P) = (term214 P).
Proof. exact (prop_ext (fun h2 : term225 m P => @lem123843 m P h2 h1) (fun h2 : term214 P => @lem123837 m P h1)). Qed.
Lemma lem123845 (m : nat) (P : nat -> Prop) (h1 : term211 m P) : term214 P.
Proof. exact (EQ_MP (@lem123844 m P h1) (@lem123837 m P h1)). Qed.
Lemma lem123846 (m : nat) (P : nat -> Prop) : term216 m P.
Proof. exact (fun h0 : term211 m P => @lem123845 m P h0). Qed.
Lemma lem123851 (P : nat -> Prop) : term220 P.
Proof. exact (fun m : nat => @lem123846 m P). Qed.
Lemma lem123856 : term224.
Proof. exact (fun P : nat -> Prop => @lem123851 P). Qed.
Lemma lem123857 : term223.
Proof. exact (EQ_MP (@lem121081) (@lem123856)). Qed.
