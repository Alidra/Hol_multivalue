Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NOT_IMP_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1820_spec.
Require Import thm1822_spec.
Require Import thm1842_spec.
Require Import thm1844_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem10201 (t1 : Prop) : term0 t1.
Proof. exact (@lem9851 t1). Qed.
Lemma lem10202 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem10203 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem10202 t1) (@lem10201 t1)). Qed.
Lemma lem10204 (t1 : Prop) (h1 : t1 = True) : t1 = True.
Proof. exact (h1). Qed.
Lemma lem10205 (t1 : Prop) (h1 : t1 = False) : t1 = False.
Proof. exact (h1). Qed.
Lemma lem10214 (t2 : Prop) : (term2 t2) = (term2 t2).
Proof. exact (eq_refl (term2 t2)). Qed.
Lemma lem10215 (t2 : Prop) (t1 : Prop) (h1 : t1 = True) : (term3 t2 t1) = (term4 t2).
Proof. exact (MK_COMB (@lem10214 t2) (@lem10204 t1 h1)). Qed.
Lemma lem10216 (t2 : Prop) : (term4 t2) = ((term5 t2) = (term6 t2)).
Proof. exact (eq_refl (term4 t2)). Qed.
Lemma lem10217 (t2 : Prop) (t1 : Prop) : (term7 t2 t1) = (term7 t2 t1).
Proof. exact (eq_refl (term7 t2 t1)). Qed.
Lemma lem10218 (t1 : Prop) (t2 : Prop) : ((term3 t2 t1) = (term4 t2)) = ((term3 t2 t1) = ((term5 t2) = (term6 t2))).
Proof. exact (MK_COMB (@lem10217 t2 t1) (@lem10216 t2)). Qed.
Lemma lem10219 (t1 : Prop) (t2 : Prop) : (term3 t2 t1) = ((term8 t1 t2) = (term9 t1 t2)).
Proof. exact (eq_refl (term3 t2 t1)). Qed.
Lemma lem10220 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem10221 (t1 : Prop) (t2 : Prop) : (term7 t2 t1) = (term10 t1 t2).
Proof. exact (MK_COMB (@lem10220) (@lem10219 t1 t2)). Qed.
Lemma lem10222 (t2 : Prop) : ((term5 t2) = (term6 t2)) = ((term5 t2) = (term6 t2)).
Proof. exact (eq_refl ((term5 t2) = (term6 t2))). Qed.
Lemma lem10223 (t1 : Prop) (t2 : Prop) : ((term3 t2 t1) = ((term5 t2) = (term6 t2))) = (((term8 t1 t2) = (term9 t1 t2)) = ((term5 t2) = (term6 t2))).
Proof. exact (MK_COMB (@lem10221 t1 t2) (@lem10222 t2)). Qed.
Lemma lem10224 (t1 : Prop) (t2 : Prop) : ((term3 t2 t1) = (term4 t2)) = (((term8 t1 t2) = (term9 t1 t2)) = ((term5 t2) = (term6 t2))).
Proof. exact (TRANS (@lem10218 t1 t2) (@lem10223 t1 t2)). Qed.
Lemma lem10225 (t2 : Prop) (t1 : Prop) (h1 : t1 = True) : ((term8 t1 t2) = (term9 t1 t2)) = ((term5 t2) = (term6 t2)).
Proof. exact (EQ_MP (@lem10224 t1 t2) (@lem10215 t2 t1 h1)). Qed.
Lemma lem10226 (t2 : Prop) (t1 : Prop) (h1 : t1 = True) : ((term5 t2) = (term6 t2)) = ((term8 t1 t2) = (term9 t1 t2)).
Proof. exact (SYM (@lem10225 t2 t1 h1)). Qed.
Lemma lem10227 (t2 : Prop) : (term2 t2) = (term2 t2).
Proof. exact (eq_refl (term2 t2)). Qed.
Lemma lem10228 (t2 : Prop) (t1 : Prop) (h1 : t1 = False) : (term3 t2 t1) = (term11 t2).
Proof. exact (MK_COMB (@lem10227 t2) (@lem10205 t1 h1)). Qed.
Lemma lem10229 (t2 : Prop) : (term11 t2) = ((term12 t2) = (term13 t2)).
Proof. exact (eq_refl (term11 t2)). Qed.
Lemma lem10230 (t2 : Prop) (t1 : Prop) : (term7 t2 t1) = (term7 t2 t1).
Proof. exact (eq_refl (term7 t2 t1)). Qed.
Lemma lem10231 (t1 : Prop) (t2 : Prop) : ((term3 t2 t1) = (term11 t2)) = ((term3 t2 t1) = ((term12 t2) = (term13 t2))).
Proof. exact (MK_COMB (@lem10230 t2 t1) (@lem10229 t2)). Qed.
Lemma lem10232 (t1 : Prop) (t2 : Prop) : (term3 t2 t1) = ((term8 t1 t2) = (term9 t1 t2)).
Proof. exact (eq_refl (term3 t2 t1)). Qed.
Lemma lem10233 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem10234 (t1 : Prop) (t2 : Prop) : (term7 t2 t1) = (term10 t1 t2).
Proof. exact (MK_COMB (@lem10233) (@lem10232 t1 t2)). Qed.
Lemma lem10235 (t2 : Prop) : ((term12 t2) = (term13 t2)) = ((term12 t2) = (term13 t2)).
Proof. exact (eq_refl ((term12 t2) = (term13 t2))). Qed.
Lemma lem10236 (t1 : Prop) (t2 : Prop) : ((term3 t2 t1) = ((term12 t2) = (term13 t2))) = (((term8 t1 t2) = (term9 t1 t2)) = ((term12 t2) = (term13 t2))).
Proof. exact (MK_COMB (@lem10234 t1 t2) (@lem10235 t2)). Qed.
Lemma lem10237 (t1 : Prop) (t2 : Prop) : ((term3 t2 t1) = (term11 t2)) = (((term8 t1 t2) = (term9 t1 t2)) = ((term12 t2) = (term13 t2))).
Proof. exact (TRANS (@lem10231 t1 t2) (@lem10236 t1 t2)). Qed.
Lemma lem10238 (t2 : Prop) (t1 : Prop) (h1 : t1 = False) : ((term8 t1 t2) = (term9 t1 t2)) = ((term12 t2) = (term13 t2)).
Proof. exact (EQ_MP (@lem10237 t1 t2) (@lem10228 t2 t1 h1)). Qed.
Lemma lem10239 (t2 : Prop) (t1 : Prop) (h1 : t1 = False) : ((term12 t2) = (term13 t2)) = ((term8 t1 t2) = (term9 t1 t2)).
Proof. exact (SYM (@lem10238 t2 t1 h1)). Qed.
Lemma lem10243 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem10244 (t2 : Prop) : (True -> t2) = t2.
Proof. exact (@lem10243 t2). Qed.
Lemma lem10245 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem10246 (t2 : Prop) : (term5 t2) = (~ t2).
Proof. exact (MK_COMB (@lem10245) (@lem10244 t2)). Qed.
Lemma lem10247 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem10248 (t2 : Prop) : (term14 t2) = (term15 t2).
Proof. exact (MK_COMB (@lem10247) (@lem10246 t2)). Qed.
Lemma lem10250 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem10251 (t2 : Prop) : (term6 t2) = (~ t2).
Proof. exact (@lem10250 (~ t2)). Qed.
Lemma lem10252 (t2 : Prop) : ((term5 t2) = (term6 t2)) = ((~ t2) = (~ t2)).
Proof. exact (MK_COMB (@lem10248 t2) (@lem10251 t2)). Qed.
Lemma lem10254 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem10255 (x : Prop) : (x = x) = True.
Proof. exact (@lem10254 Prop x). Qed.
Lemma lem10256 (t2 : Prop) : ((~ t2) = (~ t2)) = True.
Proof. exact (@lem10255 (~ t2)). Qed.
Lemma lem10257 (t2 : Prop) : ((term5 t2) = (term6 t2)) = True.
Proof. exact (TRANS (@lem10252 t2) (@lem10256 t2)). Qed.
Lemma lem10258 (t2 : Prop) : True = ((term5 t2) = (term6 t2)).
Proof. exact (SYM (@lem10257 t2)). Qed.
Lemma lem10259 (t2 : Prop) : (term5 t2) = (term6 t2).
Proof. exact (EQ_MP (@lem10258 t2) (@lem0)). Qed.
Lemma lem10263 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem10264 (t2 : Prop) : (False -> t2) = True.
Proof. exact (@lem10263 t2). Qed.
Lemma lem10265 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem10266 (t2 : Prop) : (term12 t2) = (~ True).
Proof. exact (MK_COMB (@lem10265) (@lem10264 t2)). Qed.
Lemma lem10268 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem10269 (t2 : Prop) : (term12 t2) = False.
Proof. exact (TRANS (@lem10266 t2) (@lem10268)). Qed.
Lemma lem10270 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem10271 (t2 : Prop) : (term16 t2) = (@eq Prop False).
Proof. exact (MK_COMB (@lem10270) (@lem10269 t2)). Qed.
Lemma lem10273 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem10274 (t2 : Prop) : (term13 t2) = False.
Proof. exact (@lem10273 (~ t2)). Qed.
Lemma lem10275 (t2 : Prop) : ((term12 t2) = (term13 t2)) = (False = False).
Proof. exact (MK_COMB (@lem10271 t2) (@lem10274 t2)). Qed.
Lemma lem10277 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem10278 : (False = False) = (~ False).
Proof. exact (@lem10277 False). Qed.
Lemma lem10280 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem10281 : (False = False) = True.
Proof. exact (TRANS (@lem10278) (@lem10280)). Qed.
Lemma lem10282 (t2 : Prop) : ((term12 t2) = (term13 t2)) = True.
Proof. exact (TRANS (@lem10275 t2) (@lem10281)). Qed.
Lemma lem10283 (t2 : Prop) : True = ((term12 t2) = (term13 t2)).
Proof. exact (SYM (@lem10282 t2)). Qed.
Lemma lem10284 (t2 : Prop) : (term12 t2) = (term13 t2).
Proof. exact (EQ_MP (@lem10283 t2) (@lem0)). Qed.
Lemma lem10285 (t2 : Prop) (t1 : Prop) (h1 : t1 = False) : (term8 t1 t2) = (term9 t1 t2).
Proof. exact (EQ_MP (@lem10239 t2 t1 h1) (@lem10284 t2)). Qed.
Lemma lem10286 (t2 : Prop) (t1 : Prop) (h1 : t1 = True) : (term8 t1 t2) = (term9 t1 t2).
Proof. exact (EQ_MP (@lem10226 t2 t1 h1) (@lem10259 t2)). Qed.
Lemma lem10289 (t1 : Prop) (t2 : Prop) : (term8 t1 t2) = (term9 t1 t2).
Proof. exact (or_elim (@lem10203 t1) (fun h0 : t1 = True => @lem10286 t2 t1 h0) (fun h0 : t1 = False => @lem10285 t2 t1 h0)). Qed.
Lemma lem10294 (t1 : Prop) : term17 t1.
Proof. exact (fun t2 : Prop => @lem10289 t1 t2). Qed.
Lemma lem10299 : term18.
Proof. exact (fun t1 : Prop => @lem10294 t1). Qed.
