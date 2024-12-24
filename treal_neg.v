Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import treal_neg_term_abbrevs.
Require Import FST_spec.
Require Import SND_spec.
Lemma lem1323190 : treal_neg = term0.
Proof. exact (@treal_neg_def). Qed.
Lemma lem1323191 (_23599 : prod hreal hreal) : _23599 = _23599.
Proof. exact (eq_refl _23599). Qed.
Lemma lem1323192 (_23599 : prod hreal hreal) : (treal_neg _23599) = (term1 _23599).
Proof. exact (MK_COMB (@lem1323190) (@lem1323191 _23599)). Qed.
Lemma lem1323193 (_23599 : prod hreal hreal) : (term1 _23599) = (term2 _23599).
Proof. exact (eq_refl (term1 _23599)). Qed.
Lemma lem1323194 (_23599 : prod hreal hreal) : (treal_neg _23599) = (term2 _23599).
Proof. exact (TRANS (@lem1323192 _23599) (@lem1323193 _23599)). Qed.
Lemma lem1323195 : term3.
Proof. exact (fun _23599 : prod hreal hreal => @lem1323194 _23599). Qed.
Lemma lem1323196 (_23599 : prod hreal hreal) : term4 _23599.
Proof. exact (@lem1323195 _23599). Qed.
Lemma lem1323197 (_23599 : prod hreal hreal) : (term4 _23599) = ((treal_neg _23599) = (term2 _23599)).
Proof. exact (eq_refl (term4 _23599)). Qed.
Lemma lem1323198 (_23599 : prod hreal hreal) : (treal_neg _23599) = (term2 _23599).
Proof. exact (EQ_MP (@lem1323197 _23599) (@lem1323196 _23599)). Qed.
Lemma lem1323199 (x : hreal) (y : hreal) : (term5 x y) = (term6 x y).
Proof. exact (@lem1323198 (@pair hreal hreal x y)). Qed.
Lemma lem1323200 {A B : Type'} (x : A) : term7 A B x.
Proof. exact (@lem48019 A B x). Qed.
Lemma lem1323201 {A B : Type'} (x : A) : (term7 A B x) = (term8 A B x).
Proof. exact (eq_refl (term7 A B x)). Qed.
Lemma lem1323202 {A B : Type'} (x : A) : term8 A B x.
Proof. exact (EQ_MP (@lem1323201 A B x) (@lem1323200 A B x)). Qed.
Lemma lem1323203 {A B : Type'} (x : A) (y : B) : term9 A B x y.
Proof. exact (@lem1323202 A B x y). Qed.
Lemma lem1323204 {A B : Type'} (x : A) (y : B) : (term9 A B x y) = ((term10 A B x y) = y).
Proof. exact (eq_refl (term9 A B x y)). Qed.
Lemma lem1323206 {A B : Type'} (x : A) : term11 A B x.
Proof. exact (@lem47827 A B x). Qed.
Lemma lem1323207 {A B : Type'} (x : A) : (term11 A B x) = (term12 A B x).
Proof. exact (eq_refl (term11 A B x)). Qed.
Lemma lem1323208 {A B : Type'} (x : A) : term12 A B x.
Proof. exact (EQ_MP (@lem1323207 A B x) (@lem1323206 A B x)). Qed.
Lemma lem1323209 {A B : Type'} (x : A) (y : B) : term13 A B x y.
Proof. exact (@lem1323208 A B x y). Qed.
Lemma lem1323210 {A B : Type'} (y : B) (x : A) : (term13 A B x y) = ((term14 A B x y) = x).
Proof. exact (eq_refl (term13 A B x y)). Qed.
Lemma lem1323213 {A B : Type'} (y : B) (x : A) : (term14 A B x y) = x.
Proof. exact (EQ_MP (@lem1323210 A B y x) (@lem1323209 A B x y)). Qed.
Lemma lem1323214 (y : hreal) (x : hreal) : (term15 x y) = x.
Proof. exact (@lem1323213 hreal hreal y x). Qed.
Lemma lem1323215 (x : hreal) (y : hreal) : x = (term15 x y).
Proof. exact (SYM (@lem1323214 y x)). Qed.
Lemma lem1323217 {A B : Type'} (x : A) (y : B) : (term10 A B x y) = y.
Proof. exact (EQ_MP (@lem1323204 A B x y) (@lem1323203 A B x y)). Qed.
Lemma lem1323218 (x : hreal) (y : hreal) : (term16 x y) = y.
Proof. exact (@lem1323217 hreal hreal x y). Qed.
Lemma lem1323219 (x : hreal) (y : hreal) : y = (term16 x y).
Proof. exact (SYM (@lem1323218 x y)). Qed.
Lemma lem1323220 : term17 = term17.
Proof. exact (eq_refl term17). Qed.
Lemma lem1323221 (x : hreal) (y : hreal) : (term18 x) = (term19 x y).
Proof. exact (MK_COMB (@lem1323220) (@lem1323215 x y)). Qed.
Lemma lem1323222 (x : hreal) (y : hreal) : (term19 x y) = (term20 x y).
Proof. exact (eq_refl (term19 x y)). Qed.
Lemma lem1323223 (x : hreal) : (term21 x) = (term21 x).
Proof. exact (eq_refl (term21 x)). Qed.
Lemma lem1323224 (x : hreal) (y : hreal) : ((term18 x) = (term19 x y)) = ((term18 x) = (term20 x y)).
Proof. exact (MK_COMB (@lem1323223 x) (@lem1323222 x y)). Qed.
Lemma lem1323225 (x : hreal) : (term18 x) = (term22 x).
Proof. exact (eq_refl (term18 x)). Qed.
Lemma lem1323226 : (@eq (hreal -> prod hreal hreal)) = (@eq (hreal -> prod hreal hreal)).
Proof. exact (eq_refl (@eq (hreal -> prod hreal hreal))). Qed.
Lemma lem1323227 (x : hreal) : (term21 x) = (term23 x).
Proof. exact (MK_COMB (@lem1323226) (@lem1323225 x)). Qed.
Lemma lem1323228 (x : hreal) (y : hreal) : (term20 x y) = (term20 x y).
Proof. exact (eq_refl (term20 x y)). Qed.
Lemma lem1323229 (x : hreal) (y : hreal) : ((term18 x) = (term20 x y)) = ((term22 x) = (term20 x y)).
Proof. exact (MK_COMB (@lem1323227 x) (@lem1323228 x y)). Qed.
Lemma lem1323230 (x : hreal) (y : hreal) : ((term18 x) = (term19 x y)) = ((term22 x) = (term20 x y)).
Proof. exact (TRANS (@lem1323224 x y) (@lem1323229 x y)). Qed.
Lemma lem1323231 (x : hreal) (y : hreal) : (term22 x) = (term20 x y).
Proof. exact (EQ_MP (@lem1323230 x y) (@lem1323221 x y)). Qed.
Lemma lem1323232 (x : hreal) (y : hreal) : (term24 x y) = (term25 x y).
Proof. exact (MK_COMB (@lem1323231 x y) (@lem1323219 x y)). Qed.
Lemma lem1323233 (x : hreal) (y : hreal) : (term25 x y) = (term6 x y).
Proof. exact (eq_refl (term25 x y)). Qed.
Lemma lem1323234 (x : hreal) (y : hreal) : (term26 x y) = (term26 x y).
Proof. exact (eq_refl (term26 x y)). Qed.
Lemma lem1323235 (x : hreal) (y : hreal) : ((term24 x y) = (term25 x y)) = ((term24 x y) = (term6 x y)).
Proof. exact (MK_COMB (@lem1323234 x y) (@lem1323233 x y)). Qed.
Lemma lem1323236 (y : hreal) (x : hreal) : (term24 x y) = (@pair hreal hreal y x).
Proof. exact (eq_refl (term24 x y)). Qed.
Lemma lem1323237 : (@eq (prod hreal hreal)) = (@eq (prod hreal hreal)).
Proof. exact (eq_refl (@eq (prod hreal hreal))). Qed.
Lemma lem1323238 (y : hreal) (x : hreal) : (term26 x y) = (term27 y x).
Proof. exact (MK_COMB (@lem1323237) (@lem1323236 y x)). Qed.
Lemma lem1323239 (x : hreal) (y : hreal) : (term6 x y) = (term6 x y).
Proof. exact (eq_refl (term6 x y)). Qed.
Lemma lem1323240 (x : hreal) (y : hreal) : ((term24 x y) = (term6 x y)) = ((@pair hreal hreal y x) = (term6 x y)).
Proof. exact (MK_COMB (@lem1323238 y x) (@lem1323239 x y)). Qed.
Lemma lem1323241 (x : hreal) (y : hreal) : ((term24 x y) = (term25 x y)) = ((@pair hreal hreal y x) = (term6 x y)).
Proof. exact (TRANS (@lem1323235 x y) (@lem1323240 x y)). Qed.
Lemma lem1323242 (x : hreal) (y : hreal) : (@pair hreal hreal y x) = (term6 x y).
Proof. exact (EQ_MP (@lem1323241 x y) (@lem1323232 x y)). Qed.
Lemma lem1323243 (y : hreal) (x : hreal) : (term6 x y) = (@pair hreal hreal y x).
Proof. exact (SYM (@lem1323242 x y)). Qed.
Lemma lem1323244 (y : hreal) (x : hreal) : (term5 x y) = (@pair hreal hreal y x).
Proof. exact (TRANS (@lem1323199 x y) (@lem1323243 y x)). Qed.
Lemma lem1323245 (y : hreal) : term28 y.
Proof. exact (fun x : hreal => @lem1323244 y x). Qed.
Lemma lem1323246 : term29.
Proof. exact (fun y : hreal => @lem1323245 y). Qed.
