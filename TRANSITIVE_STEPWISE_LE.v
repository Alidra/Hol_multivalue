Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import TRANSITIVE_STEPWISE_LE_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import TRANSITIVE_STEPWISE_LE_EQ_spec.
Require Import thm0_spec.
Require Import thm1820_spec.
Require Import thm1821_spec.
Require Import thm1822_spec.
Require Import thm1823_spec.
Require Import thm1842_spec.
Require Import thm1844_spec.
Require Import thm1855_spec.
Require Import thm1857_spec.
Lemma lem290152 (a : Prop) : term0 a.
Proof. exact (@lem9851 a). Qed.
Lemma lem290153 (a : Prop) : (term0 a) = (term1 a).
Proof. exact (eq_refl (term0 a)). Qed.
Lemma lem290154 (a : Prop) : term1 a.
Proof. exact (EQ_MP (@lem290153 a) (@lem290152 a)). Qed.
Lemma lem290155 (a : Prop) (h1 : a = True) : a = True.
Proof. exact (h1). Qed.
Lemma lem290156 (a : Prop) (h1 : a = False) : a = False.
Proof. exact (h1). Qed.
Lemma lem290173 (a' : Prop) (b : Prop) (c : Prop) : (term2 a' b c) = (term2 a' b c).
Proof. exact (eq_refl (term2 a' b c)). Qed.
Lemma lem290174 (a' : Prop) (b : Prop) (c : Prop) (a : Prop) (h1 : a = True) : (term3 a' b c a) = (term4 a' b c).
Proof. exact (MK_COMB (@lem290173 a' b c) (@lem290155 a h1)). Qed.
Lemma lem290175 (a' : Prop) (b : Prop) (c : Prop) : (term4 a' b c) = (term5 a' b c).
Proof. exact (eq_refl (term4 a' b c)). Qed.
Lemma lem290176 (a' : Prop) (b : Prop) (c : Prop) (a : Prop) : (term6 a' b c a) = (term6 a' b c a).
Proof. exact (eq_refl (term6 a' b c a)). Qed.
Lemma lem290177 (a : Prop) (a' : Prop) (b : Prop) (c : Prop) : ((term3 a' b c a) = (term4 a' b c)) = ((term3 a' b c a) = (term5 a' b c)).
Proof. exact (MK_COMB (@lem290176 a' b c a) (@lem290175 a' b c)). Qed.
Lemma lem290178 (a : Prop) (a' : Prop) (b : Prop) (c : Prop) : (term3 a' b c a) = (term7 a a' b c).
Proof. exact (eq_refl (term3 a' b c a)). Qed.
Lemma lem290179 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem290180 (a : Prop) (a' : Prop) (b : Prop) (c : Prop) : (term6 a' b c a) = (term8 a a' b c).
Proof. exact (MK_COMB (@lem290179) (@lem290178 a a' b c)). Qed.
Lemma lem290181 (a' : Prop) (b : Prop) (c : Prop) : (term5 a' b c) = (term5 a' b c).
Proof. exact (eq_refl (term5 a' b c)). Qed.
Lemma lem290182 (a : Prop) (a' : Prop) (b : Prop) (c : Prop) : ((term3 a' b c a) = (term5 a' b c)) = ((term7 a a' b c) = (term5 a' b c)).
Proof. exact (MK_COMB (@lem290180 a a' b c) (@lem290181 a' b c)). Qed.
Lemma lem290183 (a : Prop) (a' : Prop) (b : Prop) (c : Prop) : ((term3 a' b c a) = (term4 a' b c)) = ((term7 a a' b c) = (term5 a' b c)).
Proof. exact (TRANS (@lem290177 a a' b c) (@lem290182 a a' b c)). Qed.
Lemma lem290184 (a' : Prop) (b : Prop) (c : Prop) (a : Prop) (h1 : a = True) : (term7 a a' b c) = (term5 a' b c).
Proof. exact (EQ_MP (@lem290183 a a' b c) (@lem290174 a' b c a h1)). Qed.
Lemma lem290185 (a' : Prop) (b : Prop) (c : Prop) (a : Prop) (h1 : a = True) : (term5 a' b c) = (term7 a a' b c).
Proof. exact (SYM (@lem290184 a' b c a h1)). Qed.
Lemma lem290186 (a' : Prop) (b : Prop) (c : Prop) : (term2 a' b c) = (term2 a' b c).
Proof. exact (eq_refl (term2 a' b c)). Qed.
Lemma lem290187 (a' : Prop) (b : Prop) (c : Prop) (a : Prop) (h1 : a = False) : (term3 a' b c a) = (term9 a' b c).
Proof. exact (MK_COMB (@lem290186 a' b c) (@lem290156 a h1)). Qed.
Lemma lem290188 (a' : Prop) (b : Prop) (c : Prop) : (term9 a' b c) = (term10 a' b c).
Proof. exact (eq_refl (term9 a' b c)). Qed.
Lemma lem290189 (a' : Prop) (b : Prop) (c : Prop) (a : Prop) : (term6 a' b c a) = (term6 a' b c a).
Proof. exact (eq_refl (term6 a' b c a)). Qed.
Lemma lem290190 (a : Prop) (a' : Prop) (b : Prop) (c : Prop) : ((term3 a' b c a) = (term9 a' b c)) = ((term3 a' b c a) = (term10 a' b c)).
Proof. exact (MK_COMB (@lem290189 a' b c a) (@lem290188 a' b c)). Qed.
Lemma lem290191 (a : Prop) (a' : Prop) (b : Prop) (c : Prop) : (term3 a' b c a) = (term7 a a' b c).
Proof. exact (eq_refl (term3 a' b c a)). Qed.
Lemma lem290192 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem290193 (a : Prop) (a' : Prop) (b : Prop) (c : Prop) : (term6 a' b c a) = (term8 a a' b c).
Proof. exact (MK_COMB (@lem290192) (@lem290191 a a' b c)). Qed.
Lemma lem290194 (a' : Prop) (b : Prop) (c : Prop) : (term10 a' b c) = (term10 a' b c).
Proof. exact (eq_refl (term10 a' b c)). Qed.
Lemma lem290195 (a : Prop) (a' : Prop) (b : Prop) (c : Prop) : ((term3 a' b c a) = (term10 a' b c)) = ((term7 a a' b c) = (term10 a' b c)).
Proof. exact (MK_COMB (@lem290193 a a' b c) (@lem290194 a' b c)). Qed.
Lemma lem290196 (a : Prop) (a' : Prop) (b : Prop) (c : Prop) : ((term3 a' b c a) = (term9 a' b c)) = ((term7 a a' b c) = (term10 a' b c)).
Proof. exact (TRANS (@lem290190 a a' b c) (@lem290195 a a' b c)). Qed.
Lemma lem290197 (a' : Prop) (b : Prop) (c : Prop) (a : Prop) (h1 : a = False) : (term7 a a' b c) = (term10 a' b c).
Proof. exact (EQ_MP (@lem290196 a a' b c) (@lem290187 a' b c a h1)). Qed.
Lemma lem290198 (a' : Prop) (b : Prop) (c : Prop) (a : Prop) (h1 : a = False) : (term10 a' b c) = (term7 a a' b c).
Proof. exact (SYM (@lem290197 a' b c a h1)). Qed.
Lemma lem290204 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem290205 (a' : Prop) : (True /\ a') = a'.
Proof. exact (@lem290204 a'). Qed.
Lemma lem290206 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem290207 (a' : Prop) : (term11 a') = (imp a').
Proof. exact (MK_COMB (@lem290206) (@lem290205 a')). Qed.
Lemma lem290210 (c : Prop) (b : Prop) : (c = b) = (c = b).
Proof. exact (eq_refl (c = b)). Qed.
Lemma lem290211 (a' : Prop) (c : Prop) (b : Prop) : (term12 a' c b) = (term13 a' c b).
Proof. exact (MK_COMB (@lem290207 a') (@lem290210 c b)). Qed.
Lemma lem290214 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem290215 (a' : Prop) (c : Prop) (b : Prop) : (term14 a' c b) = (term15 a' c b).
Proof. exact (MK_COMB (@lem290214) (@lem290211 a' c b)). Qed.
Lemma lem290219 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem290220 (a' : Prop) (b : Prop) : (term16 a' b) = (a' /\ b).
Proof. exact (@lem290219 (a' /\ b)). Qed.
Lemma lem290223 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem290224 (a' : Prop) (b : Prop) : (term17 a' b) = (term18 a' b).
Proof. exact (MK_COMB (@lem290223) (@lem290220 a' b)). Qed.
Lemma lem290225 (c : Prop) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem290226 (a' : Prop) (b : Prop) (c : Prop) : (term19 a' b c) = (term20 a' b c).
Proof. exact (MK_COMB (@lem290224 a' b) (@lem290225 c)). Qed.
Lemma lem290229 (a' : Prop) (b : Prop) (c : Prop) : (term5 a' b c) = (term21 a' b c).
Proof. exact (MK_COMB (@lem290215 a' c b) (@lem290226 a' b c)). Qed.
Lemma lem290232 (a' : Prop) (b : Prop) (c : Prop) : (term21 a' b c) = (term5 a' b c).
Proof. exact (SYM (@lem290229 a' b c)). Qed.
Lemma lem290233 (a' : Prop) : term0 a'.
Proof. exact (@lem9851 a'). Qed.
Lemma lem290234 (a' : Prop) : (term0 a') = (term1 a').
Proof. exact (eq_refl (term0 a')). Qed.
Lemma lem290235 (a' : Prop) : term1 a'.
Proof. exact (EQ_MP (@lem290234 a') (@lem290233 a')). Qed.
Lemma lem290236 (a' : Prop) (h1 : a' = True) : a' = True.
Proof. exact (h1). Qed.
Lemma lem290237 (a' : Prop) (h1 : a' = False) : a' = False.
Proof. exact (h1). Qed.
Lemma lem290250 (b : Prop) (c : Prop) : (term22 b c) = (term22 b c).
Proof. exact (eq_refl (term22 b c)). Qed.
Lemma lem290251 (b : Prop) (c : Prop) (a' : Prop) (h1 : a' = True) : (term23 b c a') = (term24 b c).
Proof. exact (MK_COMB (@lem290250 b c) (@lem290236 a' h1)). Qed.
Lemma lem290252 (b : Prop) (c : Prop) : (term24 b c) = (term25 b c).
Proof. exact (eq_refl (term24 b c)). Qed.
Lemma lem290253 (b : Prop) (c : Prop) (a' : Prop) : (term26 b c a') = (term26 b c a').
Proof. exact (eq_refl (term26 b c a')). Qed.
Lemma lem290254 (a' : Prop) (b : Prop) (c : Prop) : ((term23 b c a') = (term24 b c)) = ((term23 b c a') = (term25 b c)).
Proof. exact (MK_COMB (@lem290253 b c a') (@lem290252 b c)). Qed.
Lemma lem290255 (a' : Prop) (b : Prop) (c : Prop) : (term23 b c a') = (term21 a' b c).
Proof. exact (eq_refl (term23 b c a')). Qed.
Lemma lem290256 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem290257 (a' : Prop) (b : Prop) (c : Prop) : (term26 b c a') = (term27 a' b c).
Proof. exact (MK_COMB (@lem290256) (@lem290255 a' b c)). Qed.
Lemma lem290258 (b : Prop) (c : Prop) : (term25 b c) = (term25 b c).
Proof. exact (eq_refl (term25 b c)). Qed.
Lemma lem290259 (a' : Prop) (b : Prop) (c : Prop) : ((term23 b c a') = (term25 b c)) = ((term21 a' b c) = (term25 b c)).
Proof. exact (MK_COMB (@lem290257 a' b c) (@lem290258 b c)). Qed.
Lemma lem290260 (a' : Prop) (b : Prop) (c : Prop) : ((term23 b c a') = (term24 b c)) = ((term21 a' b c) = (term25 b c)).
Proof. exact (TRANS (@lem290254 a' b c) (@lem290259 a' b c)). Qed.
Lemma lem290261 (b : Prop) (c : Prop) (a' : Prop) (h1 : a' = True) : (term21 a' b c) = (term25 b c).
Proof. exact (EQ_MP (@lem290260 a' b c) (@lem290251 b c a' h1)). Qed.
Lemma lem290262 (b : Prop) (c : Prop) (a' : Prop) (h1 : a' = True) : (term25 b c) = (term21 a' b c).
Proof. exact (SYM (@lem290261 b c a' h1)). Qed.
Lemma lem290263 (b : Prop) (c : Prop) : (term22 b c) = (term22 b c).
Proof. exact (eq_refl (term22 b c)). Qed.
Lemma lem290264 (b : Prop) (c : Prop) (a' : Prop) (h1 : a' = False) : (term23 b c a') = (term28 b c).
Proof. exact (MK_COMB (@lem290263 b c) (@lem290237 a' h1)). Qed.
Lemma lem290265 (b : Prop) (c : Prop) : (term28 b c) = (term29 b c).
Proof. exact (eq_refl (term28 b c)). Qed.
Lemma lem290266 (b : Prop) (c : Prop) (a' : Prop) : (term26 b c a') = (term26 b c a').
Proof. exact (eq_refl (term26 b c a')). Qed.
Lemma lem290267 (a' : Prop) (b : Prop) (c : Prop) : ((term23 b c a') = (term28 b c)) = ((term23 b c a') = (term29 b c)).
Proof. exact (MK_COMB (@lem290266 b c a') (@lem290265 b c)). Qed.
Lemma lem290268 (a' : Prop) (b : Prop) (c : Prop) : (term23 b c a') = (term21 a' b c).
Proof. exact (eq_refl (term23 b c a')). Qed.
Lemma lem290269 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem290270 (a' : Prop) (b : Prop) (c : Prop) : (term26 b c a') = (term27 a' b c).
Proof. exact (MK_COMB (@lem290269) (@lem290268 a' b c)). Qed.
Lemma lem290271 (b : Prop) (c : Prop) : (term29 b c) = (term29 b c).
Proof. exact (eq_refl (term29 b c)). Qed.
Lemma lem290272 (a' : Prop) (b : Prop) (c : Prop) : ((term23 b c a') = (term29 b c)) = ((term21 a' b c) = (term29 b c)).
Proof. exact (MK_COMB (@lem290270 a' b c) (@lem290271 b c)). Qed.
Lemma lem290273 (a' : Prop) (b : Prop) (c : Prop) : ((term23 b c a') = (term28 b c)) = ((term21 a' b c) = (term29 b c)).
Proof. exact (TRANS (@lem290267 a' b c) (@lem290272 a' b c)). Qed.
Lemma lem290274 (b : Prop) (c : Prop) (a' : Prop) (h1 : a' = False) : (term21 a' b c) = (term29 b c).
Proof. exact (EQ_MP (@lem290273 a' b c) (@lem290264 b c a' h1)). Qed.
Lemma lem290275 (b : Prop) (c : Prop) (a' : Prop) (h1 : a' = False) : (term29 b c) = (term21 a' b c).
Proof. exact (SYM (@lem290274 b c a' h1)). Qed.
Lemma lem290279 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem290280 (c : Prop) (b : Prop) : (term30 c b) = (c = b).
Proof. exact (@lem290279 (c = b)). Qed.
Lemma lem290283 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem290284 (c : Prop) (b : Prop) : (term31 c b) = (term32 c b).
Proof. exact (MK_COMB (@lem290283) (@lem290280 c b)). Qed.
Lemma lem290288 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem290289 (b : Prop) : (True /\ b) = b.
Proof. exact (@lem290288 b). Qed.
Lemma lem290290 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem290291 (b : Prop) : (term11 b) = (imp b).
Proof. exact (MK_COMB (@lem290290) (@lem290289 b)). Qed.
Lemma lem290292 (c : Prop) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem290293 (b : Prop) (c : Prop) : (term33 b c) = (b -> c).
Proof. exact (MK_COMB (@lem290291 b) (@lem290292 c)). Qed.
Lemma lem290296 (b : Prop) (c : Prop) : (term25 b c) = (term34 b c).
Proof. exact (MK_COMB (@lem290284 c b) (@lem290293 b c)). Qed.
Lemma lem290301 (b : Prop) (c : Prop) : (term34 b c) = (term25 b c).
Proof. exact (SYM (@lem290296 b c)). Qed.
Lemma lem290302 (c : Prop) : term0 c.
Proof. exact (@lem9851 c). Qed.
Lemma lem290303 (c : Prop) : (term0 c) = (term1 c).
Proof. exact (eq_refl (term0 c)). Qed.
Lemma lem290304 (c : Prop) : term1 c.
Proof. exact (EQ_MP (@lem290303 c) (@lem290302 c)). Qed.
Lemma lem290305 (c : Prop) (h1 : c = True) : c = True.
Proof. exact (h1). Qed.
Lemma lem290306 (c : Prop) (h1 : c = False) : c = False.
Proof. exact (h1). Qed.
Lemma lem290317 (b : Prop) : (term35 b) = (term35 b).
Proof. exact (eq_refl (term35 b)). Qed.
Lemma lem290318 (b : Prop) (c : Prop) (h1 : c = True) : (term36 b c) = (term37 b).
Proof. exact (MK_COMB (@lem290317 b) (@lem290305 c h1)). Qed.
Lemma lem290319 (b : Prop) : (term37 b) = (term38 b).
Proof. exact (eq_refl (term37 b)). Qed.
Lemma lem290320 (b : Prop) (c : Prop) : (term39 b c) = (term39 b c).
Proof. exact (eq_refl (term39 b c)). Qed.
Lemma lem290321 (c : Prop) (b : Prop) : ((term36 b c) = (term37 b)) = ((term36 b c) = (term38 b)).
Proof. exact (MK_COMB (@lem290320 b c) (@lem290319 b)). Qed.
Lemma lem290322 (b : Prop) (c : Prop) : (term36 b c) = (term34 b c).
Proof. exact (eq_refl (term36 b c)). Qed.
Lemma lem290323 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem290324 (b : Prop) (c : Prop) : (term39 b c) = (term40 b c).
Proof. exact (MK_COMB (@lem290323) (@lem290322 b c)). Qed.
Lemma lem290325 (b : Prop) : (term38 b) = (term38 b).
Proof. exact (eq_refl (term38 b)). Qed.
Lemma lem290326 (c : Prop) (b : Prop) : ((term36 b c) = (term38 b)) = ((term34 b c) = (term38 b)).
Proof. exact (MK_COMB (@lem290324 b c) (@lem290325 b)). Qed.
Lemma lem290327 (c : Prop) (b : Prop) : ((term36 b c) = (term37 b)) = ((term34 b c) = (term38 b)).
Proof. exact (TRANS (@lem290321 c b) (@lem290326 c b)). Qed.
Lemma lem290328 (b : Prop) (c : Prop) (h1 : c = True) : (term34 b c) = (term38 b).
Proof. exact (EQ_MP (@lem290327 c b) (@lem290318 b c h1)). Qed.
Lemma lem290329 (b : Prop) (c : Prop) (h1 : c = True) : (term38 b) = (term34 b c).
Proof. exact (SYM (@lem290328 b c h1)). Qed.
Lemma lem290330 (b : Prop) : (term35 b) = (term35 b).
Proof. exact (eq_refl (term35 b)). Qed.
Lemma lem290331 (b : Prop) (c : Prop) (h1 : c = False) : (term36 b c) = (term41 b).
Proof. exact (MK_COMB (@lem290330 b) (@lem290306 c h1)). Qed.
Lemma lem290332 (b : Prop) : (term41 b) = (term42 b).
Proof. exact (eq_refl (term41 b)). Qed.
Lemma lem290333 (b : Prop) (c : Prop) : (term39 b c) = (term39 b c).
Proof. exact (eq_refl (term39 b c)). Qed.
Lemma lem290334 (c : Prop) (b : Prop) : ((term36 b c) = (term41 b)) = ((term36 b c) = (term42 b)).
Proof. exact (MK_COMB (@lem290333 b c) (@lem290332 b)). Qed.
Lemma lem290335 (b : Prop) (c : Prop) : (term36 b c) = (term34 b c).
Proof. exact (eq_refl (term36 b c)). Qed.
Lemma lem290336 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem290337 (b : Prop) (c : Prop) : (term39 b c) = (term40 b c).
Proof. exact (MK_COMB (@lem290336) (@lem290335 b c)). Qed.
Lemma lem290338 (b : Prop) : (term42 b) = (term42 b).
Proof. exact (eq_refl (term42 b)). Qed.
Lemma lem290339 (c : Prop) (b : Prop) : ((term36 b c) = (term42 b)) = ((term34 b c) = (term42 b)).
Proof. exact (MK_COMB (@lem290337 b c) (@lem290338 b)). Qed.
Lemma lem290340 (c : Prop) (b : Prop) : ((term36 b c) = (term41 b)) = ((term34 b c) = (term42 b)).
Proof. exact (TRANS (@lem290334 c b) (@lem290339 c b)). Qed.
Lemma lem290341 (b : Prop) (c : Prop) (h1 : c = False) : (term34 b c) = (term42 b).
Proof. exact (EQ_MP (@lem290340 c b) (@lem290331 b c h1)). Qed.
Lemma lem290342 (b : Prop) (c : Prop) (h1 : c = False) : (term42 b) = (term34 b c).
Proof. exact (SYM (@lem290341 b c h1)). Qed.
Lemma lem290348 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem290349 (b : Prop) : (True = b) = b.
Proof. exact (@lem290348 b). Qed.
Lemma lem290350 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem290351 (b : Prop) : (term43 b) = (imp b).
Proof. exact (MK_COMB (@lem290350) (@lem290349 b)). Qed.
Lemma lem290353 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem290354 (b : Prop) : (b -> True) = True.
Proof. exact (@lem290353 b). Qed.
Lemma lem290355 (b : Prop) : (term38 b) = (b -> True).
Proof. exact (MK_COMB (@lem290351 b) (@lem290354 b)). Qed.
Lemma lem290357 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem290358 (b : Prop) : (b -> True) = True.
Proof. exact (@lem290357 b). Qed.
Lemma lem290359 (b : Prop) : (term38 b) = True.
Proof. exact (TRANS (@lem290355 b) (@lem290358 b)). Qed.
Lemma lem290360 (b : Prop) : True = (term38 b).
Proof. exact (SYM (@lem290359 b)). Qed.
Lemma lem290361 (b : Prop) : term38 b.
Proof. exact (EQ_MP (@lem290360 b) (@lem0)). Qed.
Lemma lem290367 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem290368 (b : Prop) : (False = b) = (~ b).
Proof. exact (@lem290367 b). Qed.
Lemma lem290369 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem290370 (b : Prop) : (term44 b) = (term45 b).
Proof. exact (MK_COMB (@lem290369) (@lem290368 b)). Qed.
Lemma lem290372 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem290373 (b : Prop) : (b -> False) = (~ b).
Proof. exact (@lem290372 b). Qed.
Lemma lem290374 (b : Prop) : (term42 b) = (term46 b).
Proof. exact (MK_COMB (@lem290370 b) (@lem290373 b)). Qed.
Lemma lem290376 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem290377 (b : Prop) : (term46 b) = True.
Proof. exact (@lem290376 (~ b)). Qed.
Lemma lem290378 (b : Prop) : (term42 b) = True.
Proof. exact (TRANS (@lem290374 b) (@lem290377 b)). Qed.
Lemma lem290379 (b : Prop) : True = (term42 b).
Proof. exact (SYM (@lem290378 b)). Qed.
Lemma lem290380 (b : Prop) : term42 b.
Proof. exact (EQ_MP (@lem290379 b) (@lem0)). Qed.
Lemma lem290381 (b : Prop) (c : Prop) (h1 : c = False) : term34 b c.
Proof. exact (EQ_MP (@lem290342 b c h1) (@lem290380 b)). Qed.
Lemma lem290382 (b : Prop) (c : Prop) (h1 : c = True) : term34 b c.
Proof. exact (EQ_MP (@lem290329 b c h1) (@lem290361 b)). Qed.
Lemma lem290384 (b : Prop) (c : Prop) : term34 b c.
Proof. exact (or_elim (@lem290304 c) (fun h0 : c = True => @lem290382 b c h0) (fun h0 : c = False => @lem290381 b c h0)). Qed.
Lemma lem290385 (b : Prop) (c : Prop) : term25 b c.
Proof. exact (EQ_MP (@lem290301 b c) (@lem290384 b c)). Qed.
Lemma lem290389 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem290390 (c : Prop) (b : Prop) : (term47 c b) = True.
Proof. exact (@lem290389 (c = b)). Qed.
Lemma lem290391 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem290392 (c : Prop) (b : Prop) : (term48 c b) = (imp True).
Proof. exact (MK_COMB (@lem290391) (@lem290390 c b)). Qed.
Lemma lem290396 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem290397 (b : Prop) : (False /\ b) = False.
Proof. exact (@lem290396 b). Qed.
Lemma lem290398 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem290399 (b : Prop) : (term49 b) = (imp False).
Proof. exact (MK_COMB (@lem290398) (@lem290397 b)). Qed.
Lemma lem290400 (c : Prop) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem290401 (b : Prop) (c : Prop) : (term50 b c) = (False -> c).
Proof. exact (MK_COMB (@lem290399 b) (@lem290400 c)). Qed.
Lemma lem290403 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem290404 (c : Prop) : (False -> c) = True.
Proof. exact (@lem290403 c). Qed.
Lemma lem290405 (b : Prop) (c : Prop) : (term50 b c) = True.
Proof. exact (TRANS (@lem290401 b c) (@lem290404 c)). Qed.
Lemma lem290406 (b : Prop) (c : Prop) : (term29 b c) = (True -> True).
Proof. exact (MK_COMB (@lem290392 c b) (@lem290405 b c)). Qed.
Lemma lem290408 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem290409 : (True -> True) = True.
Proof. exact (@lem290408 True). Qed.
Lemma lem290410 (b : Prop) (c : Prop) : (term29 b c) = True.
Proof. exact (TRANS (@lem290406 b c) (@lem290409)). Qed.
Lemma lem290411 (b : Prop) (c : Prop) : True = (term29 b c).
Proof. exact (SYM (@lem290410 b c)). Qed.
Lemma lem290412 (b : Prop) (c : Prop) : term29 b c.
Proof. exact (EQ_MP (@lem290411 b c) (@lem0)). Qed.
Lemma lem290413 (b : Prop) (c : Prop) (a' : Prop) (h1 : a' = False) : term21 a' b c.
Proof. exact (EQ_MP (@lem290275 b c a' h1) (@lem290412 b c)). Qed.
Lemma lem290414 (b : Prop) (c : Prop) (a' : Prop) (h1 : a' = True) : term21 a' b c.
Proof. exact (EQ_MP (@lem290262 b c a' h1) (@lem290385 b c)). Qed.
Lemma lem290416 (a' : Prop) (b : Prop) (c : Prop) : term21 a' b c.
Proof. exact (or_elim (@lem290235 a') (fun h0 : a' = True => @lem290414 b c a' h0) (fun h0 : a' = False => @lem290413 b c a' h0)). Qed.
Lemma lem290417 (a' : Prop) (b : Prop) (c : Prop) : term5 a' b c.
Proof. exact (EQ_MP (@lem290232 a' b c) (@lem290416 a' b c)). Qed.
Lemma lem290423 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem290424 (a' : Prop) : (False /\ a') = False.
Proof. exact (@lem290423 a'). Qed.
Lemma lem290425 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem290426 (a' : Prop) : (term49 a') = (imp False).
Proof. exact (MK_COMB (@lem290425) (@lem290424 a')). Qed.
Lemma lem290429 (c : Prop) (b : Prop) : (c = b) = (c = b).
Proof. exact (eq_refl (c = b)). Qed.
Lemma lem290430 (a' : Prop) (c : Prop) (b : Prop) : (term51 a' c b) = (term47 c b).
Proof. exact (MK_COMB (@lem290426 a') (@lem290429 c b)). Qed.
Lemma lem290432 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem290433 (c : Prop) (b : Prop) : (term47 c b) = True.
Proof. exact (@lem290432 (c = b)). Qed.
Lemma lem290434 (a' : Prop) (c : Prop) (b : Prop) : (term51 a' c b) = True.
Proof. exact (TRANS (@lem290430 a' c b) (@lem290433 c b)). Qed.
Lemma lem290435 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem290436 (a' : Prop) (c : Prop) (b : Prop) : (term52 a' c b) = (imp True).
Proof. exact (MK_COMB (@lem290435) (@lem290434 a' c b)). Qed.
Lemma lem290440 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem290441 (a' : Prop) (b : Prop) : (term53 a' b) = False.
Proof. exact (@lem290440 (a' /\ b)). Qed.
Lemma lem290442 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem290443 (a' : Prop) (b : Prop) : (term54 a' b) = (imp False).
Proof. exact (MK_COMB (@lem290442) (@lem290441 a' b)). Qed.
Lemma lem290444 (c : Prop) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem290445 (a' : Prop) (b : Prop) (c : Prop) : (term55 a' b c) = (False -> c).
Proof. exact (MK_COMB (@lem290443 a' b) (@lem290444 c)). Qed.
Lemma lem290447 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem290448 (c : Prop) : (False -> c) = True.
Proof. exact (@lem290447 c). Qed.
Lemma lem290449 (a' : Prop) (b : Prop) (c : Prop) : (term55 a' b c) = True.
Proof. exact (TRANS (@lem290445 a' b c) (@lem290448 c)). Qed.
Lemma lem290450 (a' : Prop) (b : Prop) (c : Prop) : (term10 a' b c) = (True -> True).
Proof. exact (MK_COMB (@lem290436 a' c b) (@lem290449 a' b c)). Qed.
Lemma lem290452 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem290453 : (True -> True) = True.
Proof. exact (@lem290452 True). Qed.
Lemma lem290454 (a' : Prop) (b : Prop) (c : Prop) : (term10 a' b c) = True.
Proof. exact (TRANS (@lem290450 a' b c) (@lem290453)). Qed.
Lemma lem290455 (a' : Prop) (b : Prop) (c : Prop) : True = (term10 a' b c).
Proof. exact (SYM (@lem290454 a' b c)). Qed.
Lemma lem290456 (a' : Prop) (b : Prop) (c : Prop) : term10 a' b c.
Proof. exact (EQ_MP (@lem290455 a' b c) (@lem0)). Qed.
Lemma lem290457 (a' : Prop) (b : Prop) (c : Prop) (a : Prop) (h1 : a = False) : term7 a a' b c.
Proof. exact (EQ_MP (@lem290198 a' b c a h1) (@lem290456 a' b c)). Qed.
Lemma lem290458 (a' : Prop) (b : Prop) (c : Prop) (a : Prop) (h1 : a = True) : term7 a a' b c.
Proof. exact (EQ_MP (@lem290185 a' b c a h1) (@lem290417 a' b c)). Qed.
Lemma lem290461 (a : Prop) (a' : Prop) (b : Prop) (c : Prop) : term7 a a' b c.
Proof. exact (or_elim (@lem290154 a) (fun h0 : a = True => @lem290458 a' b c a h0) (fun h0 : a = False => @lem290457 a' b c a h0)). Qed.
Lemma lem290462 (a : Prop) (a' : Prop) (b : Prop) (c : Prop) (h1 : term7 a a' b c) : term7 a a' b c.
Proof. exact (h1). Qed.
Lemma lem290463 (a : Prop) (a' : Prop) (c : Prop) (b : Prop) (h1 : term56 a a' c b) : term56 a a' c b.
Proof. exact (h1). Qed.
Lemma lem290464 (a : Prop) (a' : Prop) (b : Prop) (c : Prop) (h1 : term56 a a' c b) (h2 : term7 a a' b c) : term57 a a' b c.
Proof. exact (@lem290462 a a' b c h2 (@lem290463 a a' c b h1)). Qed.
Lemma lem290465 (a : Prop) (a' : Prop) (c : Prop) (b : Prop) (h1 : term56 a a' c b) : term58 a a' b c.
Proof. exact (fun h0 : term7 a a' b c => @lem290464 a a' b c h1 h0). Qed.
Lemma lem290466 (a : Prop) (a' : Prop) (b : Prop) (c : Prop) (h1 : term7 a a' b c) : term7 a a' b c.
Proof. exact (h1). Qed.
Lemma lem290467 (a : Prop) (a' : Prop) (b : Prop) (c : Prop) (h1 : term56 a a' c b) (h2 : term7 a a' b c) : term57 a a' b c.
Proof. exact (@lem290465 a a' c b h1 (@lem290466 a a' b c h2)). Qed.
Lemma lem290468 (a : Prop) (a' : Prop) (b : Prop) (c : Prop) (h1 : term7 a a' b c) : term7 a a' b c.
Proof. exact (fun h0 : term56 a a' c b => @lem290467 a a' b c h0 h1). Qed.
Lemma lem290469 (a : Prop) (a' : Prop) (b : Prop) (c : Prop) : term59 a a' b c.
Proof. exact (fun h0 : term7 a a' b c => @lem290468 a a' b c h0). Qed.
Lemma lem290472 (a : Prop) (a' : Prop) (b : Prop) (c : Prop) : term7 a a' b c.
Proof. exact (@lem290469 a a' b c (@lem290461 a a' b c)). Qed.
Lemma lem290473 (R : type1605) : term60 R.
Proof. exact (@lem290472 (term61 R) (term62 R) (term63 R) (term64 R)). Qed.
Lemma lem290474 (R : type1605) : term65 R.
Proof. exact (@lem290135 R). Qed.
Lemma lem290475 (R : type1605) : (term65 R) = (term66 R).
Proof. exact (eq_refl (term65 R)). Qed.
Lemma lem290478 (R : type1605) : term66 R.
Proof. exact (EQ_MP (@lem290475 R) (@lem290474 R)). Qed.
Lemma lem290479 (R : type1605) : term67 R.
Proof. exact (@lem290473 R (@lem290478 R)). Qed.
Lemma lem290484 : term68.
Proof. exact (fun R : type1605 => @lem290479 R). Qed.
