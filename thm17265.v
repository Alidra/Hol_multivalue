Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm17265_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1820_spec.
Require Import thm1822_spec.
Require Import thm1831_spec.
Require Import thm1833_spec.
Require Import thm1855_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem17169 (p : Prop) : term0 p.
Proof. exact (@lem9851 p). Qed.
Lemma lem17170 (p : Prop) : (term0 p) = (term1 p).
Proof. exact (eq_refl (term0 p)). Qed.
Lemma lem17171 (p : Prop) : term1 p.
Proof. exact (EQ_MP (@lem17170 p) (@lem17169 p)). Qed.
Lemma lem17172 (p : Prop) (h1 : p = True) : p = True.
Proof. exact (h1). Qed.
Lemma lem17173 (p : Prop) (h1 : p = False) : p = False.
Proof. exact (h1). Qed.
Lemma lem17182 (q : Prop) : (term2 q) = (term2 q).
Proof. exact (eq_refl (term2 q)). Qed.
Lemma lem17183 (q : Prop) (p : Prop) (h1 : p = True) : (term3 q p) = (term4 q).
Proof. exact (MK_COMB (@lem17182 q) (@lem17172 p h1)). Qed.
Lemma lem17184 (q : Prop) : (term4 q) = ((True -> q) = (term5 q)).
Proof. exact (eq_refl (term4 q)). Qed.
Lemma lem17185 (q : Prop) (p : Prop) : (term6 q p) = (term6 q p).
Proof. exact (eq_refl (term6 q p)). Qed.
Lemma lem17186 (p : Prop) (q : Prop) : ((term3 q p) = (term4 q)) = ((term3 q p) = ((True -> q) = (term5 q))).
Proof. exact (MK_COMB (@lem17185 q p) (@lem17184 q)). Qed.
Lemma lem17187 (p : Prop) (q : Prop) : (term3 q p) = ((p -> q) = (term7 p q)).
Proof. exact (eq_refl (term3 q p)). Qed.
Lemma lem17188 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem17189 (p : Prop) (q : Prop) : (term6 q p) = (term8 p q).
Proof. exact (MK_COMB (@lem17188) (@lem17187 p q)). Qed.
Lemma lem17190 (q : Prop) : ((True -> q) = (term5 q)) = ((True -> q) = (term5 q)).
Proof. exact (eq_refl ((True -> q) = (term5 q))). Qed.
Lemma lem17191 (p : Prop) (q : Prop) : ((term3 q p) = ((True -> q) = (term5 q))) = (((p -> q) = (term7 p q)) = ((True -> q) = (term5 q))).
Proof. exact (MK_COMB (@lem17189 p q) (@lem17190 q)). Qed.
Lemma lem17192 (p : Prop) (q : Prop) : ((term3 q p) = (term4 q)) = (((p -> q) = (term7 p q)) = ((True -> q) = (term5 q))).
Proof. exact (TRANS (@lem17186 p q) (@lem17191 p q)). Qed.
Lemma lem17193 (q : Prop) (p : Prop) (h1 : p = True) : ((p -> q) = (term7 p q)) = ((True -> q) = (term5 q)).
Proof. exact (EQ_MP (@lem17192 p q) (@lem17183 q p h1)). Qed.
Lemma lem17194 (q : Prop) (p : Prop) (h1 : p = True) : ((True -> q) = (term5 q)) = ((p -> q) = (term7 p q)).
Proof. exact (SYM (@lem17193 q p h1)). Qed.
Lemma lem17195 (q : Prop) : (term2 q) = (term2 q).
Proof. exact (eq_refl (term2 q)). Qed.
Lemma lem17196 (q : Prop) (p : Prop) (h1 : p = False) : (term3 q p) = (term9 q).
Proof. exact (MK_COMB (@lem17195 q) (@lem17173 p h1)). Qed.
Lemma lem17197 (q : Prop) : (term9 q) = ((False -> q) = (term10 q)).
Proof. exact (eq_refl (term9 q)). Qed.
Lemma lem17198 (q : Prop) (p : Prop) : (term6 q p) = (term6 q p).
Proof. exact (eq_refl (term6 q p)). Qed.
Lemma lem17199 (p : Prop) (q : Prop) : ((term3 q p) = (term9 q)) = ((term3 q p) = ((False -> q) = (term10 q))).
Proof. exact (MK_COMB (@lem17198 q p) (@lem17197 q)). Qed.
Lemma lem17200 (p : Prop) (q : Prop) : (term3 q p) = ((p -> q) = (term7 p q)).
Proof. exact (eq_refl (term3 q p)). Qed.
Lemma lem17201 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem17202 (p : Prop) (q : Prop) : (term6 q p) = (term8 p q).
Proof. exact (MK_COMB (@lem17201) (@lem17200 p q)). Qed.
Lemma lem17203 (q : Prop) : ((False -> q) = (term10 q)) = ((False -> q) = (term10 q)).
Proof. exact (eq_refl ((False -> q) = (term10 q))). Qed.
Lemma lem17204 (p : Prop) (q : Prop) : ((term3 q p) = ((False -> q) = (term10 q))) = (((p -> q) = (term7 p q)) = ((False -> q) = (term10 q))).
Proof. exact (MK_COMB (@lem17202 p q) (@lem17203 q)). Qed.
Lemma lem17205 (p : Prop) (q : Prop) : ((term3 q p) = (term9 q)) = (((p -> q) = (term7 p q)) = ((False -> q) = (term10 q))).
Proof. exact (TRANS (@lem17199 p q) (@lem17204 p q)). Qed.
Lemma lem17206 (q : Prop) (p : Prop) (h1 : p = False) : ((p -> q) = (term7 p q)) = ((False -> q) = (term10 q)).
Proof. exact (EQ_MP (@lem17205 p q) (@lem17196 q p h1)). Qed.
Lemma lem17207 (q : Prop) (p : Prop) (h1 : p = False) : ((False -> q) = (term10 q)) = ((p -> q) = (term7 p q)).
Proof. exact (SYM (@lem17206 q p h1)). Qed.
Lemma lem17211 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem17212 (q : Prop) : (True -> q) = q.
Proof. exact (@lem17211 q). Qed.
Lemma lem17213 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem17214 (q : Prop) : (term11 q) = (@eq Prop q).
Proof. exact (MK_COMB (@lem17213) (@lem17212 q)). Qed.
Lemma lem17218 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem17219 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem17220 : term12 = (or False).
Proof. exact (MK_COMB (@lem17219) (@lem17218)). Qed.
Lemma lem17221 (q : Prop) : q = q.
Proof. exact (eq_refl q). Qed.
Lemma lem17222 (q : Prop) : (term5 q) = (False \/ q).
Proof. exact (MK_COMB (@lem17220) (@lem17221 q)). Qed.
Lemma lem17224 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem17225 (q : Prop) : (False \/ q) = q.
Proof. exact (@lem17224 q). Qed.
Lemma lem17226 (q : Prop) : (term5 q) = q.
Proof. exact (TRANS (@lem17222 q) (@lem17225 q)). Qed.
Lemma lem17227 (q : Prop) : ((True -> q) = (term5 q)) = (q = q).
Proof. exact (MK_COMB (@lem17214 q) (@lem17226 q)). Qed.
Lemma lem17229 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem17230 (x : Prop) : (x = x) = True.
Proof. exact (@lem17229 Prop x). Qed.
Lemma lem17231 (q : Prop) : (q = q) = True.
Proof. exact (@lem17230 q). Qed.
Lemma lem17232 (q : Prop) : ((True -> q) = (term5 q)) = True.
Proof. exact (TRANS (@lem17227 q) (@lem17231 q)). Qed.
Lemma lem17233 (q : Prop) : True = ((True -> q) = (term5 q)).
Proof. exact (SYM (@lem17232 q)). Qed.
Lemma lem17234 (q : Prop) : (True -> q) = (term5 q).
Proof. exact (EQ_MP (@lem17233 q) (@lem0)). Qed.
Lemma lem17238 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem17239 (q : Prop) : (False -> q) = True.
Proof. exact (@lem17238 q). Qed.
Lemma lem17240 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem17241 (q : Prop) : (term13 q) = (@eq Prop True).
Proof. exact (MK_COMB (@lem17240) (@lem17239 q)). Qed.
Lemma lem17245 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem17246 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem17247 : term14 = (or True).
Proof. exact (MK_COMB (@lem17246) (@lem17245)). Qed.
Lemma lem17248 (q : Prop) : q = q.
Proof. exact (eq_refl q). Qed.
Lemma lem17249 (q : Prop) : (term10 q) = (True \/ q).
Proof. exact (MK_COMB (@lem17247) (@lem17248 q)). Qed.
Lemma lem17251 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem17252 (q : Prop) : (True \/ q) = True.
Proof. exact (@lem17251 q). Qed.
Lemma lem17253 (q : Prop) : (term10 q) = True.
Proof. exact (TRANS (@lem17249 q) (@lem17252 q)). Qed.
Lemma lem17254 (q : Prop) : ((False -> q) = (term10 q)) = (True = True).
Proof. exact (MK_COMB (@lem17241 q) (@lem17253 q)). Qed.
Lemma lem17256 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem17257 : (True = True) = True.
Proof. exact (@lem17256 True). Qed.
Lemma lem17258 (q : Prop) : ((False -> q) = (term10 q)) = True.
Proof. exact (TRANS (@lem17254 q) (@lem17257)). Qed.
Lemma lem17259 (q : Prop) : True = ((False -> q) = (term10 q)).
Proof. exact (SYM (@lem17258 q)). Qed.
Lemma lem17260 (q : Prop) : (False -> q) = (term10 q).
Proof. exact (EQ_MP (@lem17259 q) (@lem0)). Qed.
Lemma lem17261 (q : Prop) (p : Prop) (h1 : p = False) : (p -> q) = (term7 p q).
Proof. exact (EQ_MP (@lem17207 q p h1) (@lem17260 q)). Qed.
Lemma lem17262 (q : Prop) (p : Prop) (h1 : p = True) : (p -> q) = (term7 p q).
Proof. exact (EQ_MP (@lem17194 q p h1) (@lem17234 q)). Qed.
Lemma lem17265 (p : Prop) (q : Prop) : (p -> q) = (term7 p q).
Proof. exact (or_elim (@lem17171 p) (fun h0 : p = True => @lem17262 q p h0) (fun h0 : p = False => @lem17261 q p h0)). Qed.
