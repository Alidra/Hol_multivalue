Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import HREAL_LE_MUL_RCANCEL_IMP_term_abbrevs.
Require Import HREAL_ADD_RDISTRIB_spec.
Require Import HREAL_LE_EXISTS_DEF_spec.
Require Import thm0_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1322169 (m : hreal) : term0 m.
Proof. exact (@lem1321767 m). Qed.
Lemma lem1322170 (m : hreal) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem1322171 (m : hreal) : term1 m.
Proof. exact (EQ_MP (@lem1322170 m) (@lem1322169 m)). Qed.
Lemma lem1322172 (m : hreal) (n : hreal) : term2 m n.
Proof. exact (@lem1322171 m n). Qed.
Lemma lem1322173 (m : hreal) (n : hreal) : (term2 m n) = (term3 m n).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem1322174 (m : hreal) (n : hreal) : term3 m n.
Proof. exact (EQ_MP (@lem1322173 m n) (@lem1322172 m n)). Qed.
Lemma lem1322175 (m : hreal) (n : hreal) (p : hreal) : term4 m n p.
Proof. exact (@lem1322174 m n p). Qed.
Lemma lem1322176 (m : hreal) (n : hreal) (p : hreal) : (term4 m n p) = ((term5 m n p) = (term6 m n p)).
Proof. exact (eq_refl (term4 m n p)). Qed.
Lemma lem1322178 (m : hreal) : term7 m.
Proof. exact (@lem1321284 m). Qed.
Lemma lem1322179 (m : hreal) : (term7 m) = (term8 m).
Proof. exact (eq_refl (term7 m)). Qed.
Lemma lem1322180 (m : hreal) : term8 m.
Proof. exact (EQ_MP (@lem1322179 m) (@lem1322178 m)). Qed.
Lemma lem1322181 (m : hreal) (n : hreal) : term9 m n.
Proof. exact (@lem1322180 m n). Qed.
Lemma lem1322182 (n : hreal) (m : hreal) : (term9 m n) = ((hreal_le m n) = (term10 n m)).
Proof. exact (eq_refl (term9 m n)). Qed.
Lemma lem1322187 (n : hreal) (m : hreal) : (hreal_le m n) = (term10 n m).
Proof. exact (EQ_MP (@lem1322182 n m) (@lem1322181 m n)). Qed.
Lemma lem1322188 (b : hreal) (a : hreal) : (hreal_le a b) = (term10 b a).
Proof. exact (@lem1322187 b a). Qed.
Lemma lem1322195 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1322196 (b : hreal) (a : hreal) : (term11 a b) = (term12 b a).
Proof. exact (MK_COMB (@lem1322195) (@lem1322188 b a)). Qed.
Lemma lem1322198 (n : hreal) (m : hreal) : (hreal_le m n) = (term10 n m).
Proof. exact (EQ_MP (@lem1322182 n m) (@lem1322181 m n)). Qed.
Lemma lem1322199 (b : hreal) (a : hreal) (c : hreal) : (term13 a b c) = (term14 b a c).
Proof. exact (@lem1322198 (hreal_mul b c) (hreal_mul a c)). Qed.
Lemma lem1322206 (b : hreal) (a : hreal) (c : hreal) : (term15 a b c) = (term16 b a c).
Proof. exact (MK_COMB (@lem1322196 b a) (@lem1322199 b a c)). Qed.
Lemma lem1322209 (a : hreal) (b : hreal) (c : hreal) : (term16 b a c) = (term15 a b c).
Proof. exact (SYM (@lem1322206 b a c)). Qed.
Lemma lem1322210 (b : hreal) (a : hreal) (h1 : term10 b a) : term10 b a.
Proof. exact (h1). Qed.
Lemma lem1322211 (b : hreal) (a : hreal) (d : hreal) (h1 : b = (hreal_add a d)) : b = (hreal_add a d).
Proof. exact (h1). Qed.
Lemma lem1322212 (a : hreal) (c : hreal) : (term17 a c) = (term17 a c).
Proof. exact (eq_refl (term17 a c)). Qed.
Lemma lem1322213 (c : hreal) (b : hreal) (a : hreal) (d : hreal) (h1 : b = (hreal_add a d)) : (term18 a c b) = (term19 c a d).
Proof. exact (MK_COMB (@lem1322212 a c) (@lem1322211 b a d h1)). Qed.
Lemma lem1322214 (d : hreal) (a : hreal) (c : hreal) : (term19 c a d) = (term20 d a c).
Proof. exact (eq_refl (term19 c a d)). Qed.
Lemma lem1322215 (a : hreal) (c : hreal) (b : hreal) : (term21 a c b) = (term21 a c b).
Proof. exact (eq_refl (term21 a c b)). Qed.
Lemma lem1322216 (b : hreal) (d : hreal) (a : hreal) (c : hreal) : ((term18 a c b) = (term19 c a d)) = ((term18 a c b) = (term20 d a c)).
Proof. exact (MK_COMB (@lem1322215 a c b) (@lem1322214 d a c)). Qed.
Lemma lem1322217 (b : hreal) (a : hreal) (c : hreal) : (term18 a c b) = (term14 b a c).
Proof. exact (eq_refl (term18 a c b)). Qed.
Lemma lem1322218 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1322219 (b : hreal) (a : hreal) (c : hreal) : (term21 a c b) = (term22 b a c).
Proof. exact (MK_COMB (@lem1322218) (@lem1322217 b a c)). Qed.
Lemma lem1322220 (d : hreal) (a : hreal) (c : hreal) : (term20 d a c) = (term20 d a c).
Proof. exact (eq_refl (term20 d a c)). Qed.
Lemma lem1322221 (b : hreal) (d : hreal) (a : hreal) (c : hreal) : ((term18 a c b) = (term20 d a c)) = ((term14 b a c) = (term20 d a c)).
Proof. exact (MK_COMB (@lem1322219 b a c) (@lem1322220 d a c)). Qed.
Lemma lem1322222 (b : hreal) (d : hreal) (a : hreal) (c : hreal) : ((term18 a c b) = (term19 c a d)) = ((term14 b a c) = (term20 d a c)).
Proof. exact (TRANS (@lem1322216 b d a c) (@lem1322221 b d a c)). Qed.
Lemma lem1322223 (c : hreal) (b : hreal) (a : hreal) (d : hreal) (h1 : b = (hreal_add a d)) : (term14 b a c) = (term20 d a c).
Proof. exact (EQ_MP (@lem1322222 b d a c) (@lem1322213 c b a d h1)). Qed.
Lemma lem1322224 (c : hreal) (b : hreal) (a : hreal) (d : hreal) (h1 : b = (hreal_add a d)) : (term20 d a c) = (term14 b a c).
Proof. exact (SYM (@lem1322223 c b a d h1)). Qed.
Lemma lem1322228 (m : hreal) (n : hreal) (p : hreal) : (term5 m n p) = (term6 m n p).
Proof. exact (EQ_MP (@lem1322176 m n p) (@lem1322175 m n p)). Qed.
Lemma lem1322229 (a : hreal) (d : hreal) (c : hreal) : (term5 a d c) = (term6 a d c).
Proof. exact (@lem1322228 a d c). Qed.
Lemma lem1322230 : (@eq hreal) = (@eq hreal).
Proof. exact (eq_refl (@eq hreal)). Qed.
Lemma lem1322231 (a : hreal) (d : hreal) (c : hreal) : (term23 a d c) = (term24 a d c).
Proof. exact (MK_COMB (@lem1322230) (@lem1322229 a d c)). Qed.
Lemma lem1322232 (a : hreal) (d : hreal) (c : hreal) : (term6 a d c) = (term6 a d c).
Proof. exact (eq_refl (term6 a d c)). Qed.
Lemma lem1322233 (a : hreal) (d : hreal) (c : hreal) : ((term5 a d c) = (term6 a d c)) = ((term6 a d c) = (term6 a d c)).
Proof. exact (MK_COMB (@lem1322231 a d c) (@lem1322232 a d c)). Qed.
Lemma lem1322235 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1322236 (x : hreal) : (x = x) = True.
Proof. exact (@lem1322235 hreal x). Qed.
Lemma lem1322237 (a : hreal) (d : hreal) (c : hreal) : ((term6 a d c) = (term6 a d c)) = True.
Proof. exact (@lem1322236 (term6 a d c)). Qed.
Lemma lem1322238 (a : hreal) (d : hreal) (c : hreal) : ((term5 a d c) = (term6 a d c)) = True.
Proof. exact (TRANS (@lem1322233 a d c) (@lem1322237 a d c)). Qed.
Lemma lem1322239 (a : hreal) (d : hreal) (c : hreal) : True = ((term5 a d c) = (term6 a d c)).
Proof. exact (SYM (@lem1322238 a d c)). Qed.
Lemma lem1322240 (a : hreal) (d : hreal) (c : hreal) : (term5 a d c) = (term6 a d c).
Proof. exact (EQ_MP (@lem1322239 a d c) (@lem0)). Qed.
Lemma lem1322241 (d : hreal) (a : hreal) (c : hreal) : term20 d a c.
Proof. exact (ex_intro (term25 d a c) (hreal_mul d c) (@lem1322240 a d c)). Qed.
Lemma lem1322242 (c : hreal) (b : hreal) (a : hreal) (d : hreal) (h1 : b = (hreal_add a d)) : term14 b a c.
Proof. exact (EQ_MP (@lem1322224 c b a d h1) (@lem1322241 d a c)). Qed.
Lemma lem1322243 (c : hreal) (b : hreal) (a : hreal) (h1 : term10 b a) : term14 b a c.
Proof. exact (ex_elim (@lem1322210 b a h1) (fun d : hreal => fun h0 : term26 b a d => @lem1322242 c b a d h0)). Qed.
Lemma lem1322244 (b : hreal) (a : hreal) (c : hreal) : term16 b a c.
Proof. exact (fun h0 : term10 b a => @lem1322243 c b a h0). Qed.
Lemma lem1322245 (a : hreal) (b : hreal) (c : hreal) : term15 a b c.
Proof. exact (EQ_MP (@lem1322209 a b c) (@lem1322244 b a c)). Qed.
Lemma lem1322250 (a : hreal) (b : hreal) : term27 a b.
Proof. exact (fun c : hreal => @lem1322245 a b c). Qed.
Lemma lem1322255 (a : hreal) : term28 a.
Proof. exact (fun b : hreal => @lem1322250 a b). Qed.
Lemma lem1322260 : term29.
Proof. exact (fun a : hreal => @lem1322255 a). Qed.
