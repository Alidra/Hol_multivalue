Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm19367_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1831_spec.
Require Import thm1833_spec.
Require Import thm1842_spec.
Require Import thm1844_spec.
Require Import thm1845_spec.
Require Import thm1855_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem19173 (a : Prop) : term0 a.
Proof. exact (@lem9851 a). Qed.
Lemma lem19174 (a : Prop) : (term0 a) = (term1 a).
Proof. exact (eq_refl (term0 a)). Qed.
Lemma lem19175 (a : Prop) : term1 a.
Proof. exact (EQ_MP (@lem19174 a) (@lem19173 a)). Qed.
Lemma lem19176 (a : Prop) (h1 : a = True) : a = True.
Proof. exact (h1). Qed.
Lemma lem19177 (a : Prop) (h1 : a = False) : a = False.
Proof. exact (h1). Qed.
Lemma lem19192 (b : Prop) (c : Prop) : (term2 b c) = (term2 b c).
Proof. exact (eq_refl (term2 b c)). Qed.
Lemma lem19193 (b : Prop) (c : Prop) (a : Prop) (h1 : a = True) : (term3 b c a) = (term4 b c).
Proof. exact (MK_COMB (@lem19192 b c) (@lem19176 a h1)). Qed.
Lemma lem19194 (b : Prop) (c : Prop) : (term4 b c) = ((term5 b c) = (term6 b c)).
Proof. exact (eq_refl (term4 b c)). Qed.
Lemma lem19195 (b : Prop) (c : Prop) (a : Prop) : (term7 b c a) = (term7 b c a).
Proof. exact (eq_refl (term7 b c a)). Qed.
Lemma lem19196 (a : Prop) (b : Prop) (c : Prop) : ((term3 b c a) = (term4 b c)) = ((term3 b c a) = ((term5 b c) = (term6 b c))).
Proof. exact (MK_COMB (@lem19195 b c a) (@lem19194 b c)). Qed.
Lemma lem19197 (a : Prop) (b : Prop) (c : Prop) : (term3 b c a) = ((term8 a b c) = (term9 a b c)).
Proof. exact (eq_refl (term3 b c a)). Qed.
Lemma lem19198 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem19199 (a : Prop) (b : Prop) (c : Prop) : (term7 b c a) = (term10 a b c).
Proof. exact (MK_COMB (@lem19198) (@lem19197 a b c)). Qed.
Lemma lem19200 (b : Prop) (c : Prop) : ((term5 b c) = (term6 b c)) = ((term5 b c) = (term6 b c)).
Proof. exact (eq_refl ((term5 b c) = (term6 b c))). Qed.
Lemma lem19201 (a : Prop) (b : Prop) (c : Prop) : ((term3 b c a) = ((term5 b c) = (term6 b c))) = (((term8 a b c) = (term9 a b c)) = ((term5 b c) = (term6 b c))).
Proof. exact (MK_COMB (@lem19199 a b c) (@lem19200 b c)). Qed.
Lemma lem19202 (a : Prop) (b : Prop) (c : Prop) : ((term3 b c a) = (term4 b c)) = (((term8 a b c) = (term9 a b c)) = ((term5 b c) = (term6 b c))).
Proof. exact (TRANS (@lem19196 a b c) (@lem19201 a b c)). Qed.
Lemma lem19203 (b : Prop) (c : Prop) (a : Prop) (h1 : a = True) : ((term8 a b c) = (term9 a b c)) = ((term5 b c) = (term6 b c)).
Proof. exact (EQ_MP (@lem19202 a b c) (@lem19193 b c a h1)). Qed.
Lemma lem19204 (b : Prop) (c : Prop) (a : Prop) (h1 : a = True) : ((term5 b c) = (term6 b c)) = ((term8 a b c) = (term9 a b c)).
Proof. exact (SYM (@lem19203 b c a h1)). Qed.
Lemma lem19205 (b : Prop) (c : Prop) : (term2 b c) = (term2 b c).
Proof. exact (eq_refl (term2 b c)). Qed.
Lemma lem19206 (b : Prop) (c : Prop) (a : Prop) (h1 : a = False) : (term3 b c a) = (term11 b c).
Proof. exact (MK_COMB (@lem19205 b c) (@lem19177 a h1)). Qed.
Lemma lem19207 (b : Prop) (c : Prop) : (term11 b c) = ((term12 b c) = (term13 b c)).
Proof. exact (eq_refl (term11 b c)). Qed.
Lemma lem19208 (b : Prop) (c : Prop) (a : Prop) : (term7 b c a) = (term7 b c a).
Proof. exact (eq_refl (term7 b c a)). Qed.
Lemma lem19209 (a : Prop) (b : Prop) (c : Prop) : ((term3 b c a) = (term11 b c)) = ((term3 b c a) = ((term12 b c) = (term13 b c))).
Proof. exact (MK_COMB (@lem19208 b c a) (@lem19207 b c)). Qed.
Lemma lem19210 (a : Prop) (b : Prop) (c : Prop) : (term3 b c a) = ((term8 a b c) = (term9 a b c)).
Proof. exact (eq_refl (term3 b c a)). Qed.
Lemma lem19211 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem19212 (a : Prop) (b : Prop) (c : Prop) : (term7 b c a) = (term10 a b c).
Proof. exact (MK_COMB (@lem19211) (@lem19210 a b c)). Qed.
Lemma lem19213 (b : Prop) (c : Prop) : ((term12 b c) = (term13 b c)) = ((term12 b c) = (term13 b c)).
Proof. exact (eq_refl ((term12 b c) = (term13 b c))). Qed.
Lemma lem19214 (a : Prop) (b : Prop) (c : Prop) : ((term3 b c a) = ((term12 b c) = (term13 b c))) = (((term8 a b c) = (term9 a b c)) = ((term12 b c) = (term13 b c))).
Proof. exact (MK_COMB (@lem19212 a b c) (@lem19213 b c)). Qed.
Lemma lem19215 (a : Prop) (b : Prop) (c : Prop) : ((term3 b c a) = (term11 b c)) = (((term8 a b c) = (term9 a b c)) = ((term12 b c) = (term13 b c))).
Proof. exact (TRANS (@lem19209 a b c) (@lem19214 a b c)). Qed.
Lemma lem19216 (b : Prop) (c : Prop) (a : Prop) (h1 : a = False) : ((term8 a b c) = (term9 a b c)) = ((term12 b c) = (term13 b c)).
Proof. exact (EQ_MP (@lem19215 a b c) (@lem19206 b c a h1)). Qed.
Lemma lem19217 (b : Prop) (c : Prop) (a : Prop) (h1 : a = False) : ((term12 b c) = (term13 b c)) = ((term8 a b c) = (term9 a b c)).
Proof. exact (SYM (@lem19216 b c a h1)). Qed.
Lemma lem19223 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem19224 (b : Prop) : (True \/ b) = True.
Proof. exact (@lem19223 b). Qed.
Lemma lem19225 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem19226 (b : Prop) : (term14 b) = (and True).
Proof. exact (MK_COMB (@lem19225) (@lem19224 b)). Qed.
Lemma lem19227 (c : Prop) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem19228 (b : Prop) (c : Prop) : (term5 b c) = (True /\ c).
Proof. exact (MK_COMB (@lem19226 b) (@lem19227 c)). Qed.
Lemma lem19230 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem19231 (c : Prop) : (True /\ c) = c.
Proof. exact (@lem19230 c). Qed.
Lemma lem19232 (b : Prop) (c : Prop) : (term5 b c) = c.
Proof. exact (TRANS (@lem19228 b c) (@lem19231 c)). Qed.
Lemma lem19233 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem19234 (b : Prop) (c : Prop) : (term15 b c) = (@eq Prop c).
Proof. exact (MK_COMB (@lem19233) (@lem19232 b c)). Qed.
Lemma lem19238 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem19239 (c : Prop) : (True /\ c) = c.
Proof. exact (@lem19238 c). Qed.
Lemma lem19240 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem19241 (c : Prop) : (term16 c) = (or c).
Proof. exact (MK_COMB (@lem19240) (@lem19239 c)). Qed.
Lemma lem19244 (b : Prop) (c : Prop) : (b /\ c) = (b /\ c).
Proof. exact (eq_refl (b /\ c)). Qed.
Lemma lem19245 (b : Prop) (c : Prop) : (term6 b c) = (term17 b c).
Proof. exact (MK_COMB (@lem19241 c) (@lem19244 b c)). Qed.
Lemma lem19248 (b : Prop) (c : Prop) : ((term5 b c) = (term6 b c)) = (c = (term17 b c)).
Proof. exact (MK_COMB (@lem19234 b c) (@lem19245 b c)). Qed.
Lemma lem19251 (b : Prop) (c : Prop) : (c = (term17 b c)) = ((term5 b c) = (term6 b c)).
Proof. exact (SYM (@lem19248 b c)). Qed.
Lemma lem19252 (c : Prop) : term0 c.
Proof. exact (@lem9851 c). Qed.
Lemma lem19253 (c : Prop) : (term0 c) = (term1 c).
Proof. exact (eq_refl (term0 c)). Qed.
Lemma lem19254 (c : Prop) : term1 c.
Proof. exact (EQ_MP (@lem19253 c) (@lem19252 c)). Qed.
Lemma lem19255 (c : Prop) (h1 : c = True) : c = True.
Proof. exact (h1). Qed.
Lemma lem19256 (c : Prop) (h1 : c = False) : c = False.
Proof. exact (h1). Qed.
Lemma lem19265 (b : Prop) : (term18 b) = (term18 b).
Proof. exact (eq_refl (term18 b)). Qed.
Lemma lem19266 (b : Prop) (c : Prop) (h1 : c = True) : (term19 b c) = (term20 b).
Proof. exact (MK_COMB (@lem19265 b) (@lem19255 c h1)). Qed.
Lemma lem19267 (b : Prop) : (term20 b) = (True = (term21 b)).
Proof. exact (eq_refl (term20 b)). Qed.
Lemma lem19268 (b : Prop) (c : Prop) : (term22 b c) = (term22 b c).
Proof. exact (eq_refl (term22 b c)). Qed.
Lemma lem19269 (c : Prop) (b : Prop) : ((term19 b c) = (term20 b)) = ((term19 b c) = (True = (term21 b))).
Proof. exact (MK_COMB (@lem19268 b c) (@lem19267 b)). Qed.
Lemma lem19270 (b : Prop) (c : Prop) : (term19 b c) = (c = (term17 b c)).
Proof. exact (eq_refl (term19 b c)). Qed.
Lemma lem19271 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem19272 (b : Prop) (c : Prop) : (term22 b c) = (term23 b c).
Proof. exact (MK_COMB (@lem19271) (@lem19270 b c)). Qed.
Lemma lem19273 (b : Prop) : (True = (term21 b)) = (True = (term21 b)).
Proof. exact (eq_refl (True = (term21 b))). Qed.
Lemma lem19274 (c : Prop) (b : Prop) : ((term19 b c) = (True = (term21 b))) = ((c = (term17 b c)) = (True = (term21 b))).
Proof. exact (MK_COMB (@lem19272 b c) (@lem19273 b)). Qed.
Lemma lem19275 (c : Prop) (b : Prop) : ((term19 b c) = (term20 b)) = ((c = (term17 b c)) = (True = (term21 b))).
Proof. exact (TRANS (@lem19269 c b) (@lem19274 c b)). Qed.
Lemma lem19276 (b : Prop) (c : Prop) (h1 : c = True) : (c = (term17 b c)) = (True = (term21 b)).
Proof. exact (EQ_MP (@lem19275 c b) (@lem19266 b c h1)). Qed.
Lemma lem19277 (b : Prop) (c : Prop) (h1 : c = True) : (True = (term21 b)) = (c = (term17 b c)).
Proof. exact (SYM (@lem19276 b c h1)). Qed.
Lemma lem19278 (b : Prop) : (term18 b) = (term18 b).
Proof. exact (eq_refl (term18 b)). Qed.
Lemma lem19279 (b : Prop) (c : Prop) (h1 : c = False) : (term19 b c) = (term24 b).
Proof. exact (MK_COMB (@lem19278 b) (@lem19256 c h1)). Qed.
Lemma lem19280 (b : Prop) : (term24 b) = (False = (term25 b)).
Proof. exact (eq_refl (term24 b)). Qed.
Lemma lem19281 (b : Prop) (c : Prop) : (term22 b c) = (term22 b c).
Proof. exact (eq_refl (term22 b c)). Qed.
Lemma lem19282 (c : Prop) (b : Prop) : ((term19 b c) = (term24 b)) = ((term19 b c) = (False = (term25 b))).
Proof. exact (MK_COMB (@lem19281 b c) (@lem19280 b)). Qed.
Lemma lem19283 (b : Prop) (c : Prop) : (term19 b c) = (c = (term17 b c)).
Proof. exact (eq_refl (term19 b c)). Qed.
Lemma lem19284 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem19285 (b : Prop) (c : Prop) : (term22 b c) = (term23 b c).
Proof. exact (MK_COMB (@lem19284) (@lem19283 b c)). Qed.
Lemma lem19286 (b : Prop) : (False = (term25 b)) = (False = (term25 b)).
Proof. exact (eq_refl (False = (term25 b))). Qed.
Lemma lem19287 (c : Prop) (b : Prop) : ((term19 b c) = (False = (term25 b))) = ((c = (term17 b c)) = (False = (term25 b))).
Proof. exact (MK_COMB (@lem19285 b c) (@lem19286 b)). Qed.
Lemma lem19288 (c : Prop) (b : Prop) : ((term19 b c) = (term24 b)) = ((c = (term17 b c)) = (False = (term25 b))).
Proof. exact (TRANS (@lem19282 c b) (@lem19287 c b)). Qed.
Lemma lem19289 (b : Prop) (c : Prop) (h1 : c = False) : (c = (term17 b c)) = (False = (term25 b)).
Proof. exact (EQ_MP (@lem19288 c b) (@lem19279 b c h1)). Qed.
Lemma lem19290 (b : Prop) (c : Prop) (h1 : c = False) : (False = (term25 b)) = (c = (term17 b c)).
Proof. exact (SYM (@lem19289 b c h1)). Qed.
Lemma lem19292 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem19293 (b : Prop) : (True = (term21 b)) = (term21 b).
Proof. exact (@lem19292 (term21 b)). Qed.
Lemma lem19295 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem19296 (b : Prop) : (term21 b) = True.
Proof. exact (@lem19295 (b /\ True)). Qed.
Lemma lem19297 (b : Prop) : (True = (term21 b)) = True.
Proof. exact (TRANS (@lem19293 b) (@lem19296 b)). Qed.
Lemma lem19298 (b : Prop) : True = (True = (term21 b)).
Proof. exact (SYM (@lem19297 b)). Qed.
Lemma lem19299 (b : Prop) : True = (term21 b).
Proof. exact (EQ_MP (@lem19298 b) (@lem0)). Qed.
Lemma lem19301 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem19302 (b : Prop) : (False = (term25 b)) = (term26 b).
Proof. exact (@lem19301 (term25 b)). Qed.
Lemma lem19304 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem19305 (b : Prop) : (term25 b) = (b /\ False).
Proof. exact (@lem19304 (b /\ False)). Qed.
Lemma lem19307 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem19308 (b : Prop) : (b /\ False) = False.
Proof. exact (@lem19307 b). Qed.
Lemma lem19309 (b : Prop) : (term25 b) = False.
Proof. exact (TRANS (@lem19305 b) (@lem19308 b)). Qed.
Lemma lem19310 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem19311 (b : Prop) : (term26 b) = (~ False).
Proof. exact (MK_COMB (@lem19310) (@lem19309 b)). Qed.
Lemma lem19313 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem19314 (b : Prop) : (term26 b) = True.
Proof. exact (TRANS (@lem19311 b) (@lem19313)). Qed.
Lemma lem19315 (b : Prop) : (False = (term25 b)) = True.
Proof. exact (TRANS (@lem19302 b) (@lem19314 b)). Qed.
Lemma lem19316 (b : Prop) : True = (False = (term25 b)).
Proof. exact (SYM (@lem19315 b)). Qed.
Lemma lem19317 (b : Prop) : False = (term25 b).
Proof. exact (EQ_MP (@lem19316 b) (@lem0)). Qed.
Lemma lem19318 (b : Prop) (c : Prop) (h1 : c = False) : c = (term17 b c).
Proof. exact (EQ_MP (@lem19290 b c h1) (@lem19317 b)). Qed.
Lemma lem19319 (b : Prop) (c : Prop) (h1 : c = True) : c = (term17 b c).
Proof. exact (EQ_MP (@lem19277 b c h1) (@lem19299 b)). Qed.
Lemma lem19321 (b : Prop) (c : Prop) : c = (term17 b c).
Proof. exact (or_elim (@lem19254 c) (fun h0 : c = True => @lem19319 b c h0) (fun h0 : c = False => @lem19318 b c h0)). Qed.
Lemma lem19322 (b : Prop) (c : Prop) : (term5 b c) = (term6 b c).
Proof. exact (EQ_MP (@lem19251 b c) (@lem19321 b c)). Qed.
Lemma lem19328 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem19329 (b : Prop) : (False \/ b) = b.
Proof. exact (@lem19328 b). Qed.
Lemma lem19330 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem19331 (b : Prop) : (term27 b) = (and b).
Proof. exact (MK_COMB (@lem19330) (@lem19329 b)). Qed.
Lemma lem19332 (c : Prop) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem19333 (b : Prop) (c : Prop) : (term12 b c) = (b /\ c).
Proof. exact (MK_COMB (@lem19331 b) (@lem19332 c)). Qed.
Lemma lem19336 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem19337 (b : Prop) (c : Prop) : (term28 b c) = (term29 b c).
Proof. exact (MK_COMB (@lem19336) (@lem19333 b c)). Qed.
Lemma lem19341 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem19342 (c : Prop) : (False /\ c) = False.
Proof. exact (@lem19341 c). Qed.
Lemma lem19343 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem19344 (c : Prop) : (term30 c) = (or False).
Proof. exact (MK_COMB (@lem19343) (@lem19342 c)). Qed.
Lemma lem19347 (b : Prop) (c : Prop) : (b /\ c) = (b /\ c).
Proof. exact (eq_refl (b /\ c)). Qed.
Lemma lem19348 (b : Prop) (c : Prop) : (term13 b c) = (term31 b c).
Proof. exact (MK_COMB (@lem19344 c) (@lem19347 b c)). Qed.
Lemma lem19350 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem19351 (b : Prop) (c : Prop) : (term31 b c) = (b /\ c).
Proof. exact (@lem19350 (b /\ c)). Qed.
Lemma lem19354 (b : Prop) (c : Prop) : (term13 b c) = (b /\ c).
Proof. exact (TRANS (@lem19348 b c) (@lem19351 b c)). Qed.
Lemma lem19355 (b : Prop) (c : Prop) : ((term12 b c) = (term13 b c)) = ((b /\ c) = (b /\ c)).
Proof. exact (MK_COMB (@lem19337 b c) (@lem19354 b c)). Qed.
Lemma lem19357 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem19358 (x : Prop) : (x = x) = True.
Proof. exact (@lem19357 Prop x). Qed.
Lemma lem19359 (b : Prop) (c : Prop) : ((b /\ c) = (b /\ c)) = True.
Proof. exact (@lem19358 (b /\ c)). Qed.
Lemma lem19360 (b : Prop) (c : Prop) : ((term12 b c) = (term13 b c)) = True.
Proof. exact (TRANS (@lem19355 b c) (@lem19359 b c)). Qed.
Lemma lem19361 (b : Prop) (c : Prop) : True = ((term12 b c) = (term13 b c)).
Proof. exact (SYM (@lem19360 b c)). Qed.
Lemma lem19362 (b : Prop) (c : Prop) : (term12 b c) = (term13 b c).
Proof. exact (EQ_MP (@lem19361 b c) (@lem0)). Qed.
Lemma lem19363 (b : Prop) (c : Prop) (a : Prop) (h1 : a = False) : (term8 a b c) = (term9 a b c).
Proof. exact (EQ_MP (@lem19217 b c a h1) (@lem19362 b c)). Qed.
Lemma lem19364 (b : Prop) (c : Prop) (a : Prop) (h1 : a = True) : (term8 a b c) = (term9 a b c).
Proof. exact (EQ_MP (@lem19204 b c a h1) (@lem19322 b c)). Qed.
Lemma lem19367 (a : Prop) (b : Prop) (c : Prop) : (term8 a b c) = (term9 a b c).
Proof. exact (or_elim (@lem19175 a) (fun h0 : a = True => @lem19364 b c a h0) (fun h0 : a = False => @lem19363 b c a h0)). Qed.
