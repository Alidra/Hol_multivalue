Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LE_NEG2_term_abbrevs.
Require Import REAL_LE_LNEG_spec.
Require Import REAL_NEG_NEG_spec.
Require Import thm1338238_spec.
Lemma lem1362226 (x : real) : term0 x.
Proof. exact (@lem1362225 x). Qed.
Lemma lem1362227 (x : real) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1362228 (x : real) : term1 x.
Proof. exact (EQ_MP (@lem1362227 x) (@lem1362226 x)). Qed.
Lemma lem1362229 (x : real) (y : real) : term2 x y.
Proof. exact (@lem1362228 x y). Qed.
Lemma lem1362230 (x : real) (y : real) : (term2 x y) = ((term3 x y) = (term4 x y)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem1362233 (x : real) (h1 : (term5 x) = x) : (term5 x) = x.
Proof. exact (h1). Qed.
Lemma lem1362234 (x : real) (h1 : (term5 x) = x) : x = (term5 x).
Proof. exact (SYM (@lem1362233 x h1)). Qed.
Lemma lem1362235 (x : real) (h1 : x = (term5 x)) : x = (term5 x).
Proof. exact (h1). Qed.
Lemma lem1362236 (x : real) (h1 : x = (term5 x)) : (term5 x) = x.
Proof. exact (SYM (@lem1362235 x h1)). Qed.
Lemma lem1362237 (x : real) : ((term5 x) = x) = (x = (term5 x)).
Proof. exact (prop_ext (fun h1 : (term5 x) = x => @lem1362234 x h1) (fun h1 : x = (term5 x) => @lem1362236 x h1)). Qed.
Lemma lem1362238 : term6 = term7.
Proof. exact (fun_ext (fun x : real => @lem1362237 x)). Qed.
Lemma lem1362239 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1362240 : term8 = term9.
Proof. exact (MK_COMB (@lem1362239) (@lem1362238)). Qed.
Lemma lem1362241 : term9.
Proof. exact (EQ_MP (@lem1362240) (@lem1358662)). Qed.
Lemma lem1362242 (x : real) : term10 x.
Proof. exact (@lem1362241 x). Qed.
Lemma lem1362243 (x : real) : (term10 x) = (x = (term5 x)).
Proof. exact (eq_refl (term10 x)). Qed.
Lemma lem1362246 (x : real) : x = (term5 x).
Proof. exact (EQ_MP (@lem1362243 x) (@lem1362242 x)). Qed.
Lemma lem1362247 (y : real) : y = (term5 y).
Proof. exact (@lem1362246 y). Qed.
Lemma lem1362248 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem1362249 (y : real) : (real_le y) = (term11 y).
Proof. exact (MK_COMB (@lem1362248) (@lem1362247 y)). Qed.
Lemma lem1362250 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1362251 (y : real) (x : real) : (real_le y x) = (term12 y x).
Proof. exact (MK_COMB (@lem1362249 y) (@lem1362250 x)). Qed.
Lemma lem1362252 (x : real) (y : real) : (term13 x y) = (term13 x y).
Proof. exact (eq_refl (term13 x y)). Qed.
Lemma lem1362253 (y : real) (x : real) : ((term14 x y) = (real_le y x)) = ((term14 x y) = (term12 y x)).
Proof. exact (MK_COMB (@lem1362252 x y) (@lem1362251 y x)). Qed.
Lemma lem1362254 (y : real) (x : real) : ((term14 x y) = (term12 y x)) = ((term14 x y) = (real_le y x)).
Proof. exact (SYM (@lem1362253 y x)). Qed.
Lemma lem1362258 (x : real) (y : real) : (term3 x y) = (term4 x y).
Proof. exact (EQ_MP (@lem1362230 x y) (@lem1362229 x y)). Qed.
Lemma lem1362259 (x : real) (y : real) : (term14 x y) = (term15 x y).
Proof. exact (@lem1362258 x (real_neg y)). Qed.
Lemma lem1362260 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1362261 (x : real) (y : real) : (term13 x y) = (term16 x y).
Proof. exact (MK_COMB (@lem1362260) (@lem1362259 x y)). Qed.
Lemma lem1362263 (x : real) (y : real) : (term3 x y) = (term4 x y).
Proof. exact (EQ_MP (@lem1362230 x y) (@lem1362229 x y)). Qed.
Lemma lem1362264 (y : real) (x : real) : (term12 y x) = (term17 y x).
Proof. exact (@lem1362263 (real_neg y) x). Qed.
Lemma lem1362265 (y : real) (x : real) : ((term14 x y) = (term12 y x)) = ((term15 x y) = (term17 y x)).
Proof. exact (MK_COMB (@lem1362261 x y) (@lem1362264 y x)). Qed.
Lemma lem1362268 (y : real) (x : real) : ((term15 x y) = (term17 y x)) = ((term14 x y) = (term12 y x)).
Proof. exact (SYM (@lem1362265 y x)). Qed.
Lemma lem1362269 : term18 = term18.
Proof. exact (eq_refl term18). Qed.
Lemma lem1362270 (x : real) : term19 x.
Proof. exact (@lem1338238 x). Qed.
Lemma lem1362271 (x : real) : (term19 x) = (term20 x).
Proof. exact (eq_refl (term19 x)). Qed.
Lemma lem1362272 (x : real) : term20 x.
Proof. exact (EQ_MP (@lem1362271 x) (@lem1362270 x)). Qed.
Lemma lem1362273 (x : real) (y : real) : term21 x y.
Proof. exact (@lem1362272 x y). Qed.
Lemma lem1362274 (y : real) (x : real) : (term21 x y) = ((real_add x y) = (real_add y x)).
Proof. exact (eq_refl (term21 x y)). Qed.
Lemma lem1362277 (y : real) (x : real) : (real_add x y) = (real_add y x).
Proof. exact (EQ_MP (@lem1362274 y x) (@lem1362273 x y)). Qed.
Lemma lem1362278 (y : real) (x : real) : (term22 x y) = (term23 y x).
Proof. exact (@lem1362277 (real_neg y) x). Qed.
Lemma lem1362279 (y : real) (x : real) : (term15 x y) = (term17 y x).
Proof. exact (MK_COMB (@lem1362269) (@lem1362278 y x)). Qed.
Lemma lem1362280 (y : real) (x : real) : (term14 x y) = (term12 y x).
Proof. exact (EQ_MP (@lem1362268 y x) (@lem1362279 y x)). Qed.
Lemma lem1362281 (y : real) (x : real) : (term14 x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1362254 y x) (@lem1362280 y x)). Qed.
Lemma lem1362286 (x : real) : term24 x.
Proof. exact (fun y : real => @lem1362281 y x). Qed.
Lemma lem1362291 : term25.
Proof. exact (fun x : real => @lem1362286 x). Qed.
